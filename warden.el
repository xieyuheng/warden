;;; warden.el --- Make dired more like warden

;; Copyright (C) 2015  Rich Alesi
;; Copyright (C) 2015  XIE Yuheng

;; Author : Rich Alesi <https://github.com/ralesi>
;; Author : XIE Yuheng

;; Based on work from
;; peep-dired - Author: Adam Sokolnicki <adam.sokolnicki@gmail.com>

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; FEATURES

;; Replaces dired buffer with features from warden
;; - show window stack of parent directories
;; - show preview window of selected directory or file
;; - fast navigation using vi-like keybindings
;; - move through navigation history
;; - copy and paste functionality utilizing a copy ring

;;; KNOWN ISSUES

;; - window specific settings neededs
;;  - history
;;  - current-file

;;; Code:

(declare-function dired-omit-mode "dired-x")
(declare-function dired-kill-tree "dired-aux")
(declare-function image-dired-display-window-height "image-dired")
(declare-function image-dired-display-window-width "image-dired")
(declare-function image-dired-create-display-image-buffer "image-dired")
(declare-function image-dired-insert-image "image-dired")
(declare-function image-dired-update-property "image-dired")
(declare-function format-spec "format-spec")

(require 'cl-lib)
(require 'dired)
(require 'hl-line)
(require 'autorevert)
(require 'bookmark)
(require 'ring)

(require 'subr-x)
(require 'diminish nil t)

(defgroup warden ()
  "Modify dired to act like warden."
  :group 'warden
  :prefix "warden-")

;; directory options
(defcustom warden-cleanup-on-disable t
  "Cleanup opened buffers when disabling the minor mode."
  :group 'warden
  :type 'boolean)

(defcustom warden-cleanup-eagerly nil
  "Cleanup opened buffers upon `warden-next-file' & `warden-prev-file'."
  :group 'warden
  :type 'boolean)

(defcustom warden-show-dotfiles nil
  "When t it will show dotfiles in directory."
  :group 'warden
  :type 'boolean)

(defcustom warden-history-length 30
  "Length of history warden will track."
  :group 'warden
  :type 'integer)

(defcustom warden-copy-ring-length 10
  "How many sets of files stored for copy and paste."
  :group 'warden
  :type 'integer)

;; preview options
(defcustom warden-excluded-extensions
  '("mkv"
    "iso"
    "mp4"
    "bin"
    "exe"
    "msi"
    "pdf"
    "djvu")
  "File extensions to not preview."
  :group 'warden
  :type 'list)

(defcustom warden-max-preview-size 2
  "File size in MB to prevent preview of files."
  :group 'warden
  :type 'integer)

(defcustom warden-listing-switches "-alGh"
  "Default listing switchs for dired buffer."
  :group 'warden
  :type 'string)

(defcustom warden-listing-dir-first t
  "Non-nil modifies dired buffer to sort directories first."
  :group 'warden
  :type 'boolean)

(defcustom warden-persistent-sort nil
  "When non-nil, sort all directories with the current flags."
  :group 'warden
  :type 'boolean)

(defcustom warden-preview-file t
  "When t preview the selected file."
  :group 'warden
  :type 'boolean)

(defcustom warden-width-preview 0.65
  "Fraction of frame width taken by preview window."
  :group 'warden
  :type 'float)

;; parent options
(defcustom warden-width-parents 0.12
  "Fraction of frame width taken by parent windows"
  :group 'warden
  :type 'float)

(defcustom warden-max-parent-width 0.42
  "The max width allocated to showing parent windows."
  :group 'warden
  :type 'float)

(defcustom warden-footer-delay 0.2
  "Time in seconds to delay running footer functions."
  :group 'warden
  :type 'float)

(defcustom warden-preview-delay 0.040
  "Time in seconds to delay running preview file functions."
  :group 'warden
  :type 'float)

(defcustom warden-dont-show-binary t
  "When non-nil, detect binary files and don't show them in the
preview window."
  :group 'warden
  :type 'boolean)

;; declare used variables
(defvar warden-mode)
(defvar dired-omit-verbose)
(defvar dired-omit-mode)
(defvar image-dired-temp-image-file)
(defvar image-dired-cmd-create-temp-image-program)
(defvar image-dired-cmd-create-temp-image-options)
(defvar image-dired-display-image-buffer)

;; global variables

(defvar warden-sorting-switches nil)
(defvar warden-window nil)
(defvar warden-buffer nil)
(defvar warden-frame nil)

(defvar warden-w-alist ()
  "List of windows using warden")

(defvar warden-f-alist ()
  "List of frames using warden")

(defvar warden-history-index 0)

(defvar warden-history-ring (make-ring warden-history-length))

(defvar warden-copy-ring (make-ring warden-copy-ring-length))

(defvar warden-image-scale-ratio 1.3)
(defvar warden-image-fit-window nil)

(defvar warden-pre-alist)
(defvar warden-pre-saved nil)
(defvar warden-pre-hl-mode nil)
(defvar warden-pre-arev-mode nil)
(defvar warden-pre-omit-mode nil)
(defvar warden-pre-dired-listing nil)

(defvar warden-preview-window nil)
(defvar warden-preview-buffers ()
  "List with buffers of previewed files.")

(defvar warden-parent-windows nil)
(defvar warden-parent-buffers ()
  "List with buffers of parent buffers.")
(defvar warden-parent-dirs nil)

(defvar warden-visited-buffers ()
  "List of buffers visited in warden")

;; frame specific variables
(defvar warden-subdir-p nil)

;; buffer local variables

(defvar warden-current-file nil)
;; (make-variable-buffer-local 'warden-current-file)

(defvar warden-child-name nil)
(make-variable-buffer-local 'warden-child-name)

;; hooks
(defvar warden-mode-load-hook nil)
(defvar warden-parent-dir-hook
  '(revert-buffer
    dired-hide-details-mode
    warden-sort
    warden-hide-dotfiles
    warden-omit
    auto-revert-mode
    warden-sub-window-setup))

;; maps
(defvar warden-dired-map nil
  "Mapping for dired prefix.")

(defvar warden-mode-map
  (let ((map (make-sparse-keymap)))

    ;; build off of dired commands
    ;; (set-keymap-parent map dired-mode-map)

    (define-key map [left]        'warden-up-directory)
    (define-key map [down]        'warden-next-file)
    (define-key map [up]          'warden-prev-file)
    (define-key map [right]       'warden-find-file)
    (define-key map (kbd "RET")   'warden-find-file)

    (define-key map "?"           'warden-help)
    (define-key map "'"           'warden-show-size)
    (define-key map "!"           'shell-command)
    (define-key map "B"           'warden-show-bookmarks)
    (define-key map "D"           'dired-do-delete)
    (define-key map "G"           'warden-goto-bottom)
    (define-key map "H"           'warden-prev-history)
    (define-key map "I"           'warden-insert-subdir)
    (define-key map "J"           'warden-next-subdir)
    (define-key map "K"           'warden-prev-subdir)
    (define-key map "L"           'warden-next-history)
    (define-key map "R"           'dired-do-rename)
    (define-key map "S"           'warden-pop-eshell)
    (define-key map "["           'warden-prev-parent)
    (define-key map "]"           'warden-next-parent)
    (define-key map "f"           'warden-search-files)
    (define-key map "gg"          'warden-goto-top)
    (define-key map "gh"          'warden-go-home)

    (define-key map "m"           'warden-create-mark)
    (define-key map "o"           'warden-sort-criteria)
    (define-key map "q"           'warden-disable)
    (define-key map "u"           'dired-unmark)
    (define-key map "v"           'dired-toggle-marks)
    (define-key map "zz"          'warden-show-history)

    ;; copy and paste
    (define-key map "yy"          'warden-copy)
    (define-key map "dd"          'warden-cut)
    (define-key map "pp"          'warden-paste)
    (define-key map "po"          'warden-paste-over)
    (define-key map "p?"          'warden-show-copy-contents)

    ;; settings
    (define-key map "zh"          'warden-toggle-dotfiles)
    (define-key map "zf"          'warden-toggle-scale-images)

    ;;
    (define-key map (kbd "C-r")   'isearch-backward)
    (define-key map (kbd "C-t")   'isearch-forward)

    (define-key map (kbd "C-SPC") 'warden-mark)
    (define-key map (kbd "TAB")   'warden-mark)
    (define-key map (kbd "`")     'warden-goto-mark)

    ;; define a prefix for all dired commands
    (define-prefix-command 'warden-dired-map nil "Dired-prefix")
    (setq warden-dired-map (copy-tree dired-mode-map))
    (define-key map ";" warden-dired-map)

    map)
  "Define mappings for warden-mode." )


;;; frame parameter helpers

(defmacro r--fget (var &optional frame)
  "Return the value of `VAR', looks for buffer local version first."
  (let ((parameter (intern (format "%s" var))))
    `(or
      (when (local-variable-if-set-p (quote ,parameter))
        (buffer-local-value (quote ,parameter) (current-buffer)))
      (frame-parameter ,frame (quote ,parameter))
      ,var)))

(defmacro r--fset (var val &optional frame buffer-local)
  "Set the value of `VAR' in local buffer and on frame. When `BUFFER-LOCAL' is
non-nil, set buffer local variable as well."
  (let ((parameter (intern (format "%s" var))))
    `(progn
       (when ,buffer-local
         (set (make-local-variable (quote ,parameter)) ,val))
       (modify-frame-parameters ,frame (list (cons (quote  ,parameter) ,val)))
       ;; (message "%s" (frame-parameter nil ,parameter))
       )))

(defmacro r--fclear (parameter)
  `(r--fset ,parameter nil))

;;; alist helpers

(defun r--aget (alist key)
  "Return the value of KEY in ALIST. Uses `assoc'.
If PARAM is not found, return nil."
  (cdr-safe (assoc key alist)))

(defun r--akeys (alist)
  "Return the value of KEY in ALIST. Uses `assoc'.
If PARAM is not found, return nil."
  (mapcar 'car alist))

(defmacro r--aput (alist key value &optional no-overwrite)
  "Remove key from alist and set key with value. Set `NO-OVERWRITE' to non-nil
to not replace existing value."
  `(let ((sublist (assoc ,key ,alist)))
     (if sublist
         (unless ,no-overwrite
           (setcdr sublist ,value))
         (push (cons ,key ,value) ,alist))))

(defmacro r--aremove (alist key)
  "Remove KEY's key-value-pair from ALIST."
  `(setq ,alist (delq (assoc ,key ,alist) ,alist)))


;; data structures
(cl-defstruct (warden-window (:constructor warden--track-window))
  prev-buffer curr-buffer history)

;; mappings

(defun warden-define-additional-maps (&optional mode)
  "Define additional mappings for warden-mode that can't simply be in the defvar (depend on packages)."


  ;; normalize keymaps to work with evil mode
  (with-eval-after-load "evil"
    ;; turn off evilified buffers for evilify usage
    (evil-define-key 'visual warden-mode-map "u" 'dired-unmark)
    (evil-define-key 'normal warden-mode-map
                     "V"            'evil-visual-line
                     "n"            'evil-search-next
                     "N"            'evil-search-previous)
    (when (and (fboundp 'evil-evilified-state-p)
               (evil-evilified-state-p))
      (evil-evilified-state -1)
      (evil-normal-state))
    (evil-make-intercept-map warden-mode-map 'normal)
    (evil-normalize-keymaps))

  ;; and simulating search in standard emacs
  (unless (featurep 'evil)
    (define-key warden-mode-map "/" 'isearch-forward)
    (define-key warden-mode-map "n" 'isearch-repeat-forward)
    (define-key warden-mode-map "N" 'isearch-repeat-backward)
    ;; make sure isearch is cleared before we delete the buffer on exit
    (add-hook 'warden-mode-hook '(lambda () (setq isearch--current-buffer nil)))))


;; copy / paste
(defun warden-show-copy-ring (copy-index)
  "Show copy ring in `warden-copy-ring', selection inserts at top for use."
  (interactive (list
                (completing-read "Select from copy ring: "
                                 (warden--ring-elements
                                  warden-copy-ring)))))

(defun warden-update-copy-ring (move append)
  "Add marked files to `warden-copy-ring'. When `MOVE' is non-nil, targets will
be moved. `APPEND' will add files to current ring."
  ;; ideas borrowed from Fuco1's `dired-warden' package.
  (let ((marked-files (dired-get-marked-files)))
    (if (or (ring-empty-p warden-copy-ring)
            (not append))
        (ring-insert warden-copy-ring (cons move marked-files))
        (let* ((current (ring-remove warden-copy-ring 0))
               (cur-files (cdr current)))
          (ring-insert warden-copy-ring
                       (cons move
                             (cl-remove-duplicates
                              (append cur-files marked-files)
                              :test (lambda (x y) (or (null y) (equal x y)))
                              )))))
    (warden-show-flags)
    (message (format "%s %d item(s) to %s ring [total:%d]"
                     (if append "Added" "Copied")
                     (length marked-files)
                     (if move "cut" "copy")
                     (length (cdr (ring-ref warden-copy-ring 0)))))))

(defun warden-mark (arg &optional interactive)
  "Mark the file at point in the Dired buffer.
If the region is active, mark all files in the region.
Otherwise, with a prefix arg, mark files on the next ARG lines."
  (interactive (list current-prefix-arg t))
  (cond
    ;; Mark files in the active region.
    ((and interactive (use-region-p))
     (save-excursion
       (let ((beg (region-beginning))
             (end (region-end)))
         (dired-mark-files-in-region
          (progn (goto-char beg) (line-beginning-position))
          (progn (goto-char end) (line-beginning-position))))))
    ;; Mark the current (or next ARG) files.
    (t
     (let ((inhibit-read-only t))
       (dired-repeat-over-lines
        (prefix-numeric-value arg)
        (function (lambda () (delete-char 1) (insert dired-marker-char))))))))

(defun warden-copy (&optional append)
  "Place selected files in the copy ring and mark to be copied.
`universal-argument' can be used to append to current copy ring."
  (interactive "P")
  (warden-update-copy-ring nil append))

(defun warden-cut (&optional append)
  "Place selected files in the copy ring and mark to be moved.
`universal-argument' can be used to append to current copy ring."
  (interactive "P")
  (warden-update-copy-ring t append))

(defun warden-paste (&optional overwrite link)
  "Paste copied files from topmost copy ring."
  (interactive)
  (let* ((current (ring-ref warden-copy-ring 0))
         (move (car current))
         (fileset (cdr current))
         (target (dired-current-directory))
         (filenum 0))
    (cl-loop for file in fileset do
             (when (file-exists-p file)
               (if move
                   (rename-file file target overwrite)
                   (if (file-directory-p file)
                       (copy-directory file target)
                       (copy-file file target overwrite)))
               (setq filenum (+ filenum 1))))
    ;; show immediate changes in buffer
    (revert-buffer)
    (message (format "%s %d/%d item(s) from the copy ring."
                     (if move "Moved" "Copied")
                     filenum
                     (length fileset)
                     ))))

(defun warden-paste-over ()
  "Paste and overwrite copied files when same file names exist."
  (interactive)
  (warden-paste t))

(defun warden-show-copy-contents ()
  "Show the current contents to be copied / moved"
  (interactive)
  (let* ((current (ring-ref warden-copy-ring 0))
         (move (if (car current) "Move" "Copy"))
         (fileset (cdr current)))
    (message (format "%s - total size: %s\n%s"
                     (propertize move 'face 'font-lock-builtin-face)
                     (warden--get-file-sizes fileset)
                     (propertize (string-join fileset "\n") 'face 'font-lock-comment-face)
                     ))))

(defun warden-pop-eshell (&optional arg)
  (interactive)
  (let* ((eshell-buffer-name "*eshell*")
         (buf
          (cond
            ((numberp arg)
             (get-buffer-create (format "%s<%d>"
                                        eshell-buffer-name
                                        arg)))
            (arg
             (generate-new-buffer eshell-buffer-name))
            (t
             (get-buffer-create eshell-buffer-name)
             ))))
    (cl-assert (and buf (buffer-live-p buf)))
    (split-window-below)
    (windmove-down)
    (pop-to-buffer-same-window buf)
    (unless (derived-mode-p 'eshell-mode)
      (eshell-mode))
    buf))



;;; delayed function creation

(defmacro warden-define-delayed (func-sym delay)
  "Define a delayed version of FUNC-SYM with delay time DELAY.
When called, a delayed function only runs after the idle time
specified by DELAY. Multiple calls to the same function before
the idle timer fires are ignored."
  (let* ((func-str (symbol-name func-sym))
         (new-func (intern (format "%s-delayed" func-str)))
         (time-var (intern (format "%s-delay-time" func-str)))
         (timer (intern (format "%s-delay-timer" func-str))))
    `(progn (defvar ,time-var ,delay)
            (defvar ,timer nil)
            (defun ,new-func ()
              ,(format "Delayed version of %s" func-str)
              (unless (timerp ,timer)
                (setq ,timer
                      (run-with-idle-timer
                       ,delay nil
                       (lambda ()
                         (,func-sym)
                         (setq ,timer nil)))))))))

;; define delayed functions
(warden-define-delayed warden-details-message warden-footer-delay)
(warden-define-delayed warden-setup-preview warden-preview-delay)

;; marks
(defun warden-show-bookmarks ()
  "Show bookmark prompt for all bookmarked directories."
  (interactive)
  (let ((bookmark
         (completing-read "Select from bookmarks: "
                          (warden--directory-bookmarks) )))
    (when bookmark (warden-find-file bookmark))))

(defun warden--directory-bookmarks ()
  "Return a list of all bookmarks linking to a directory."
  (cl-remove-duplicates
   (cl-loop for bm in bookmark-alist
            for fname = (alist-get 'filename bm)
            when (file-directory-p fname) collect fname into new
            finally return new)
   :test (lambda (x y) (or (null y) (equal x y)))))

(defun warden-create-mark (mark)
  "Create new bookmark using internal bookmarks, designating bookmark name as
warden-`CHAR'."
  (interactive "cm-")
  (let ((mark-letter (char-to-string mark)))
    (bookmark-set (concat "warden-" mark-letter))
    (message "Bookmarked directory %s as `warden-%s'"
             default-directory mark-letter)))

(defun warden-goto-mark ()
  "Go to bookmarks specified from `warden-create-mark'."
  (interactive)
  (let* ((mark
          (read-key
           (mapconcat
            #'(lambda (bm)
                (when (and
                       (string-match "warden-" (car  bm))
                       (file-directory-p (cdr (cadr bm))))
                  (replace-regexp-in-string "warden-" "" (car bm))))
            bookmark-alist " ")))
         (mark-letter (char-to-string mark))
         (bookmark-name (concat "warden-" mark-letter))
         (bookmark-path (bookmark-location bookmark-name)))
    (when (file-directory-p bookmark-path)
      (warden-find-file bookmark-path))))

;; ring utilities
(defun warden--ring-elements (ring)
  "Return deduplicated elements of `ring'"
  (delq nil
        (cl-remove-duplicates
         (ring-elements ring)
         :test (lambda (x y) (or (null y) (equal x y)))
         )))

(defun warden--ring-index-elements (ring)
  "Return elements of `ring', along with its index in a (cons)."
  (let (listing)
    (dotimes (idx (ring-length ring) listing)
      (setq listing (append (cons idx (ring-ref ring idx)) listing)))))

;; history
(defun warden-show-history (history)
  "Show history prompt for recent directories"
  (interactive
   (list
    (completing-read "Select from history: "
                     (warden--ring-elements warden-history-ring))))
  (when history (warden-find-file history)))

(defun warden-jump-history (jump)
  "Move through history ring by increment `jump'"
  (let* ((ring warden-history-ring)
         (curr-index warden-history-index)
         (goto-idx (min
                    (max 0 (+ curr-index jump))
                    (- (ring-length ring) 1)))
         (jump-history (ring-ref ring goto-idx)))
    (message (format "warden-history : %i/%i" (+ 1 goto-idx) (ring-length warden-history-ring)))
    (when jump-history
      (setq warden-history-index goto-idx)
      (warden-find-file jump-history t))))

(defun warden-next-history ()
  "Move forward in history"
  (interactive)
  (warden-jump-history -1))

(defun warden-prev-history ()
  "Move backward in history"
  (interactive)
  (warden-jump-history 1))

;; primary window functions
(defun warden-refresh ()
  "Refresh evil warden buffer."
  (interactive)
  ;; make sure cursor is visible on screen
  (scroll-right)
  ;; reset dired trees
  (dired-kill-tree dired-directory)
  ;; refresh for any changes
  (revert-buffer)
  ;; setup buffer
  (warden-setup)
  (warden-show-details))

(defun warden-help ()
  "Show help message for warden basics."
  (interactive)
  (message "[h/l]-back/forward [j/k]-up/down [f]ind-file [i]nspect-file [^R]eload [S]hell [H/L]-history back/forward"))

(defun warden-toggle-dotfiles ()
  "Show/hide dot-files."
  (interactive)
  (if warden-show-dotfiles ; if currently showing
      (progn
        (setq warden-show-dotfiles nil)
        (warden-hide-dotfiles))
      (progn
        (setq warden-show-dotfiles t)
        (revert-buffer) ; otherwise just revert to re-show
        ))
  (warden-setup)
  (message (format "Show Dotfiles: %s"  warden-show-dotfiles)))

(defun warden-hide-dotfiles ()
  "Hide dotfiles in directory. TODO add variable for files to hide."
  (unless warden-show-dotfiles
    (dired-mark-if
     (and (not (looking-at-p dired-re-dot))
          (not (eolp))			; empty line
          (let ((fn (dired-get-filename t t)))
            (and fn (string-match-p  "^\\\." fn))))
     nil)
    (dired-do-kill-lines nil "")))

(defun warden-sort-criteria (criteria)
  "Call sort-dired by different `CRITERIA'."
  (interactive
   (list
    (read-char-choice
     "criteria: (n/N)ame (e/E)xt (s/S)ize m(t/T)ime (c/C)time " '(?q ?n ?N ?e ?E ?s ?S ?t ?T ?c ?C))))
  (unless (eq criteria ?q)
    (let* ((c (char-to-string criteria))
           (uppercasep (and (stringp c) (string-equal c (upcase c)) ))
           (cc (downcase c))
           (warden-sort-flag
            (cond
              ((string-equal cc "n") "")
              ((string-equal cc "c") "c")
              ((string-equal cc "e") "X")
              ((string-equal cc "t") "t")
              ((string-equal cc "s") "S")))
           )
      (setq warden-sorting-switches
            (concat warden-sort-flag
                    (when uppercasep "r")))
      (warden-sort t)
      (warden-refresh))))

(defun warden-omit ()
  "Quietly omit files in dired."
  (setq-local dired-omit-verbose nil)
  ;; (setq-local dired-omit-files "^\\.?#\\|^\\.$\\|^\\.\\.$\\|^\\.")
  (dired-omit-mode t))

(defun warden-sort (&optional force)
  "Perform current sort on directory. Specify `FORCE' to sort even when
`warden-persistent-sort' is nil."
  (when (or force
            warden-persistent-sort)
    (dired-sort-other
     (concat dired-listing-switches
             warden-sorting-switches))))


(defun warden-toggle-scale-images ()
  "Show/hide dot-files."
  (interactive)
  (if warden-image-fit-window ; if currently showing
      (setq warden-image-fit-window nil)
      (setq warden-image-fit-window t))
  (when warden-preview-file
    (warden-setup-preview))
  (message (format "Fit Images to Window: %s"  warden-image-fit-window)))



;; dired navigation
(defun warden-search-files ()
  "Search for files / directories in folder."
  (interactive)
  (if (featurep 'helm)
      (call-interactively 'helm-find-files)
      (call-interactively 'ido-find-file)))

(defun warden-up-directory ()
  "Move to parent directory."
  (interactive)
  (let ((current default-directory)
        (parent (warden-parent-directory default-directory)))
    (when parent
      (warden-find-file parent)
      (dired-goto-file current))))

(defun warden-save-window-settings (&optional overwrite)
  (let ((frame (window-frame))
        (window (selected-window)))
    (r--aput warden-f-alist
             frame
             (current-window-configuration)
             (null overwrite))
    (r--aput warden-w-alist
             window
             (cons (current-buffer) nil)
             (null overwrite))))

;; ><><><
(defun warden-find-file (&optional entry)
  (interactive)
  (let ((find-name
         (or entry
             (dired-get-filename nil t))))
    (when find-name
      (if (file-directory-p find-name)
          (let ()
            (warden-save-window-settings)
            (switch-to-buffer
             (dired-noselect find-name))
            (warden-mode 1))
          (let ()
            (message "'q' to exit warden, and leave the viewing buffer"))))))

(defun warden-disable ()
  "Interactively disable warden-mode."
  (interactive)
  (let ((find-name (dired-get-filename nil t)))
    (if (file-directory-p find-name)
        (let ()
          (message "can not exit warden when viewing a dir"))
        (let ()
          (delete-window)))))

(defun warden-insert-subdir ()
  "Insert subdir from selected folder."
  (interactive)
  (let ((find-name (dired-get-filename nil t)))
    (if (file-directory-p find-name)
        (progn
          (setq warden-subdir-p t)
          (dired-insert-subdir find-name)
          (revert-buffer)
          (warden-setup))
        (message "Can only insert on a directory."))))

(defun warden-prev-subdir ()
  "Go to previous subdir in warden buffer."
  (interactive)
  (dired-prev-subdir 1 t)
  (beginning-of-line))

(defun warden-next-subdir ()
  "Go to next subdir in warden buffer."
  (interactive)
  (dired-next-subdir 1 t)
  (beginning-of-line))

(defun warden-update-history (name)
  "Update history ring and current index"
  (when (or (ring-empty-p warden-history-ring)
            (not (eq name (ring-ref warden-history-ring 0))))
    (progn
      (ring-insert warden-history-ring (directory-file-name name))
      (setq warden-history-index 0))))

(defun warden-goto-top ()
  "Move to top of file list"
  (interactive)
  (goto-char (point-min))
  (warden-prev-file))

(defun warden-goto-bottom ()
  "Move to top of file list"
  (interactive)
  (goto-char (point-max))
  (warden-next-file))

(defun warden-go-home ()
  "Move to top of file list"
  (interactive)
  (goto-char (point-max))
  (warden-find-file "~/"))

(defun warden-next-file ()
  "Move to next file in warden."
  (interactive)
  (dired-next-line 1)
  (when (eobp)
    (dired-next-line -1))
  (warden-show-details)
  (when warden-preview-file
    (when (get-buffer "*warden-prev*")
      (with-current-buffer "*warden-prev*"
        (erase-buffer)))
    (warden-setup-preview-delayed)))

(defun warden-prev-file ()
  "Move to previous file in warden."
  (interactive)
  (dired-previous-line 1)
  (warden-show-details)
  (when warden-preview-file
    (when (get-buffer "*warden-prev*")
      (with-current-buffer "*warden-prev*"
        (erase-buffer)))
    (warden-setup-preview-delayed)))

(defun warden--footer-spec ())

(defun warden-show-size ()
  "Show directory size."
  (interactive)
  (warden-details-message t))

(defun warden-show-details ()
  (warden-update-current-file)
  (warden-details-message-delayed))

(defun warden-details-message (&optional sizes)
  "Echo file details"
  (when (dired-get-filename nil t)
    (let* ((entry (dired-get-filename nil t))
           ;; enable to troubleshoot speeds
           ;; (sizes t)
           (filename (file-name-nondirectory entry))
           (fattr (file-attributes entry))
           (fwidth (frame-width))
           (file-size (if sizes (concat "File "
                                        (file-size-human-readable (nth 7 fattr))) "Press \' for size info."))
           (dir-size (if sizes (concat "Dir " (warden--get-file-sizes
                                               (warden--get-file-listing
                                                dired-directory)
                                               ;; (list dired-directory)
                                               ))
                         ""))
           (user (nth 2 fattr))
           (file-mount
            (if sizes
                (or (let ((index 0)
                          size
                          return)
                      (dolist (mount (warden--get-mount-partitions 'mount)
                               return)
                        (when (string-match (concat "^" mount "/.*") entry)
                          (setq size
                                (nth index
                                     (warden--get-mount-partitions 'avail)))
                          (setq return (format "Free%s (%s)" size mount)))
                        (setq index (+ index 1))
                        ))
                    "") ""))
           (filedir-size (if sizes (warden--get-file-sizes
                                    (warden--get-file-listing dired-directory))
                             ""))
           (file-date (format-time-string "%Y-%m-%d %H:%m"
                                          (nth 5 fattr)))
           (file-perm (nth 8 fattr))
           (cur-pos (line-number-at-pos (point)))
           (final-pos (- (line-number-at-pos (point-max)) 1))
           (position (format "%3d/%-3d"
                             cur-pos
                             final-pos))
           (footer-spec (warden--footer-spec))
           (lhs (format
                 "%s %s"
                 (propertize file-date 'face 'font-lock-warning-face)
                 file-perm))
           (rhs (format
                 "%s %s %s %s"
                 file-size
                 dir-size
                 file-mount
                 position
                 ))
           (space (- fwidth
                     (length lhs)))
           (message-log-max nil)
           (msg
            (format
             ;; "%s"
             (format  "%%s%%%ds" space)
             lhs
             rhs
             )))
      (message "%s" msg))))

(defun warden-update-current-file ()
  (r--fset warden-current-file
           (or
            (dired-get-filename nil t)
            dired-directory) nil t))



;; parent window functions
(defun warden-sub-window-setup ()
  "Parent window options."
  ;; allow mouse click to jump to that directory
  (make-local-variable 'mouse-1-click-follows-link)
  (setq mouse-1-click-follows-link nil)
  (local-set-key (kbd  "<mouse-1>") 'warden-find-file))

(defun warden-parent-child-select ()
  (when warden-child-name
    (dired-goto-file warden-child-name)
    (hl-line-mode t)))

(defun warden-setup-parents ()
  "Setup all parent directories."
  (let ((parent-name (warden-parent-directory default-directory))
        (current-name default-directory)
        (i 0)
        (unused-windows ()))

    (setq warden-buffer (current-buffer))

    (setq warden-window (get-buffer-window (current-buffer)))

    (setq warden-visited-buffers (append warden-parent-buffers warden-visited-buffers))

    (setq warden-parent-buffers ())
    (setq warden-parent-windows ())
    (setq warden-parent-dirs ())
    (mapc 'warden-make-parent warden-parent-dirs)

    ;; select child folder in each parent
    (save-excursion
      (walk-window-tree
       (lambda (window)
         (progn
           (when (member window warden-parent-windows)
             ;; select-window needed for hl-line
             (select-window window)
             (warden-parent-child-select))))
       nil nil 'nomini))

    (select-window warden-window)
    ))

(defun warden-make-parent (parent)
  "Make parent window.  `PARENT' is a construct with ((current . parent) .
slot)."
  (let* ((parent-name (cdar parent))
         (current-name (caar parent))
         (slot (cdr parent))
         (parent-buffer (warden-dir-buffer parent-name))
         (parent-window
          (display-buffer
           parent-buffer
           `(warden-display-buffer-at-side . ((side . left)
                                              (slot . ,(- 0 slot))
                                              (inhibit-same-window . t)
                                              (window-width . ,(min
                                                                (/ warden-max-parent-width
                                                                   (length warden-parent-dirs))
                                                                warden-width-parents)))))))
    (with-current-buffer parent-buffer
      (setq warden-child-name (directory-file-name current-name)))

    (add-to-list 'warden-parent-buffers parent-buffer)
    (add-to-list 'warden-parent-windows parent-window)))

(defun warden-next-parent ()
  "Move up in parent directory"
  (interactive)
  (with-current-buffer (car warden-parent-buffers)
    (dired-next-line 1)
    (let ((curfile (dired-get-filename nil t)))
      (if (file-directory-p curfile)
          (warden-find-file curfile)
          (dired-next-line -1)))))

(defun warden-prev-parent ()
  "Move up in parent directory"
  (interactive)
  (with-current-buffer (car warden-parent-buffers)
    (dired-next-line -1)
    (let ((curfile (dired-get-filename nil t)))
      (if (file-directory-p curfile)
          (warden-find-file curfile)
          (dired-next-line 1)))))


;; window creation subroutines
(defun warden-dir-buffer (entry)
  "Open `ENTRY' in dired buffer."
  ;; (ignore-errors
  (with-current-buffer (or
                        (car (or (dired-buffers-for-dir entry) ()))
                        (dired-noselect entry))
    (run-hooks 'warden-parent-dir-hook)
    (current-buffer)))

(defun warden-dir-contents (entry)
  "Open `ENTRY' in dired buffer."
  (let ((temp-buffer (or (get-buffer "*warden-prev*")
                         (generate-new-buffer "*warden-prev*"))))
    (with-demoted-errors
        (with-current-buffer temp-buffer
          (make-local-variable 'font-lock-defaults)
          (setq font-lock-defaults '((dired-font-lock-keywords) nil t))
          (buffer-disable-undo)
          (erase-buffer)
          (turn-on-font-lock)
          (insert-directory entry (concat dired-listing-switches warden-sorting-switches) nil t)
          (goto-char (point-min))
          ;; truncate lines in directory buffer
          (setq truncate-lines t)
          ;; remove . and .. from directory listing
          (save-excursion
            (while (re-search-forward "total used in directory\\|\\.$" nil t)
              ;; (beginning-of-line)
              (delete-region (progn (forward-line 0) (point))
                             (progn (forward-line 1) (point)))))
          (current-buffer)))))

(defun warden-preview-buffer (entry-name)
  "Create the preview buffer of `ENTRY-NAME'."
  ;; show file
  ;; (if (image-type-from-file-header entry-name)
  (if (and (image-type-from-file-header entry-name)
           (not (eq (image-type-from-file-header entry-name) 'gif))
           warden-image-fit-window)
      (warden-setup-image-preview entry-name)
      (with-current-buffer
          (or (find-buffer-visiting entry-name)
              (find-file-noselect entry-name nil nil))
        (current-buffer))))

(defun warden-setup-image-preview (entry-name)
  "Setup and maybe resize image"
  (let* ((new-file (expand-file-name image-dired-temp-image-file))
         (file (expand-file-name entry-name))
         ret success
         (width (* warden-width-preview warden-image-scale-ratio (image-dired-display-window-width)))
         (height (image-dired-display-window-height))
         (image-type 'jpeg) command)
    (if (and (not (eq (image-type-from-file-header entry-name) 'gif))
             warden-image-fit-window)
        (progn
          (setq command
                (format-spec
                 image-dired-cmd-create-temp-image-options
                 (list
                  (cons ?p image-dired-cmd-create-temp-image-program)
                  (cons ?w width)
                  (cons ?h height)
                  (cons ?f file)
                  (cons ?t new-file))))
          (setq ret (call-process shell-file-name nil nil nil
                                  shell-command-switch command))
          (when (= 0 ret)
            (setq success 1))))
    (with-current-buffer (image-dired-create-display-image-buffer)
      (let ((inhibit-read-only t))
        (erase-buffer)
        (clear-image-cache)
        (image-dired-insert-image (if success
                                      image-dired-temp-image-file
                                      file)
                                  image-type 0 0)
        (goto-char (point-min))
        (image-dired-update-property 'original-file-name file))
      image-dired-display-image-buffer)))

(defun warden-setup-preview ()
  "Setup warden preview window."
  (let* ((entry-name (dired-get-filename nil t))
         (inhibit-modification-hooks t)
         (fsize
          (nth 7 (file-attributes entry-name))))
    (when warden-cleanup-eagerly
      (warden-preview-cleanup))
    ;; delete existing preview window
    (when (and warden-preview-window
               (window-live-p warden-preview-window))
      (ignore-errors (delete-window warden-preview-window)))
    (when (and entry-name
               warden-preview-file)
      (unless (or
               (> fsize (* 1024 1024 warden-max-preview-size))
               (member (file-name-extension entry-name)
                       warden-excluded-extensions))
        (with-demoted-errors "%S"
          (let* ((dir (file-directory-p entry-name))
                 (preview-buffer (if dir
                                     (warden-dir-contents entry-name)
                                     (warden-preview-buffer entry-name)))
                 preview-window)
            (unless (and (not dir) warden-dont-show-binary (warden--prev-binary-p))
              (setq preview-window
                    (display-buffer
                     preview-buffer
                     `(warden-display-buffer-at-side
                       . ((side . right)
                          (slot . 1)
                          ;; (inhibit-same-window . t)
                          (window-width . ,(- warden-width-preview
                                              (min (- warden-max-parent-width warden-width-parents)
                                                   (* (- 0 1) warden-width-parents)))))))))
            (add-to-list 'warden-preview-buffers preview-buffer)
            (setq warden-preview-window preview-window)
            (dired-hide-details-mode t)))))))


;; utilities
(defun warden-parent-directory (entry)
  "Find the parent directory of `ENTRY'."
  (file-name-directory (directory-file-name entry)))

;; (defun warden-fix-width (window)
;;   "Fix the width of `WINDOW'."
;;   (with-selected-window window
;;     (setq-local window-size-fixed 'width)))

(defun warden--get-file-sizes (fileset)
  "Determine file size of provided list of files in `FILESET'."
  (if (and
       fileset
       (executable-find "du"))
      (with-temp-buffer
        (apply 'call-process "du" nil t nil "-sch" fileset)
        (format "%s"
                (progn
                  (re-search-backward "\\(^[0-9.,]+[A-Za-z]+\\).*total$")
                  (match-string 1)))) ""))

(defun warden--get-mount-partitions (mode)
  "Determine device information."
  (if (executable-find "df")
      (with-temp-buffer
        (apply 'call-process "df" nil t t
               (list  "-h"
                      (concat "--output="
                              (cl-case mode
                                ('mount
                                 (if (eq system-type 'windows-nt)
                                     "source"
                                     "target"))
                                ('avail "avail")
                                ('size "size")))))
        (nreverse
         (cdr (split-string
               (replace-regexp-in-string "\n$" "" (buffer-string)) "[\n\r]+"))))
      ()))

(defun warden--get-file-listing (dir)
  "Return listing of files in dired directory."
  (save-excursion
    (let ((fileset ())
          file buffer-read-only)
      (goto-char (point-min))
      (while (not (eobp))
        (save-excursion
          (and (not (looking-at-p dired-re-dir))
               (not (eolp))
               (setq file (dired-get-filename nil t)) ; nil on non-file
               (progn (end-of-line)
                      (push file fileset))))
        (forward-line 1))
      fileset)))

(defun warden-display-buffer-at-side (buffer alist)
  "Try displaying `BUFFER' at one side of the selected frame. This splits the
window at the designated `side' of the frame.  Accepts `window-width' as a
fraction of the total frame size"
  (let* ((side (or (cdr (assq 'side alist)) 'bottom))
         (slot (or (cdr (assq 'slot alist)) 0))
         (window-width (or (cdr (assq 'window-width alist)) 0.5))
         (window-size (ceiling  (* (frame-width) window-width)))
         (split-width-threshold 0)
         (current-window warden-window)
         new-window
         reuse-window)

    ;; (walk-window-tree
    ;;  (lambda (window)
    ;;    (progn
    ;;      (when (not (eq current-window window))
    ;;        (when (eq (window-parameter window 'window-slot) slot)
    ;;          (setq reuse-window window))
    ;;        (when (eq (window-parameter window 'window-slot) (+ slot 1))
    ;;          (setq current-window window))
    ;;        )))
    ;;  nil nil 'nomini)

    ;; (if reuse-window
    ;;     (progn
    ;;       (shrink-window (-  window-size (window-width reuse-window)) t)
    ;;       ;; (set-window-parameter reuse-window 'window-slot slot)
    ;;       (window--display-buffer
    ;;        buffer reuse-window 'reuse alist display-buffer-mark-dedicated)
    ;;       )
    (progn
      (setq new-window (split-window current-window window-size side))
      (set-window-parameter new-window 'window-slot slot)
      (window--display-buffer
       buffer new-window 'window alist display-buffer-mark-dedicated))
    ;; )
    ))

(defun warden-show-flags ()
  "Show copy / paste flags in warden buffer."
  (when (not (ring-empty-p warden-copy-ring))
    (warden-clear-flags ?P)
    (warden-clear-flags ?M)
    ;; (dired-unmark-all-files ?\r)
    (let* ((current (ring-ref warden-copy-ring 0))
           (fileset (cdr current))
           (dired-marker-char (if (car current) ?M ?P)))
      (save-excursion
        (cl-loop for file in fileset do
                 (when
                     (dired-goto-file file)
                   (warden-mark 1)))))))

(defun warden-clear-flags (mark)
  "Remove a copy / paste flags from every file."
  (save-excursion
    (let* ((count 0)
           (inhibit-read-only t) case-fold-search
           (string (format "\n%c" mark)))
      (goto-char (point-min))
      (while
          (search-forward string nil t)
        (when (dired-get-filename t t)
          (subst-char-in-region (1- (point)) (point)
                                (preceding-char) ?\s))))))

;; Idea from http://emacs.stackexchange.com/questions/10277/make-emacs-automatically-open-binary-files-in-hexl-mode
(defun warden--prev-binary-p ()
  (when (get-buffer "*warden-prev*")
    (with-current-buffer "*warden-prev*"
      (save-excursion
        (goto-char (point-min))
        (search-forward (string ?\x00) nil t 1)))))


;; cleanup and reversion
(defun warden-preview-cleanup ()
  "Cleanup all old buffers and windows used by warden."
  (mapc 'warden-kill-buffer warden-preview-buffers)
  (setq warden-preview-buffers ()))

(defun warden-kill-buffer (buffer)
  "Delete unmodified buffers and any dired buffer"
  (when
      (and (buffer-live-p buffer)
           (eq 'dired-mode (buffer-local-value 'major-mode buffer)))
    ;; (not (buffer-modified-p buffer))
    (kill-buffer buffer)))



(defun warden-revert (&optional buffer)
  "Revert warden settings."
  ;; restore window configuration

  (let* ((warden-window-props
          (r--aget warden-w-alist
                   (selected-window)))
         (prev-buffer (car warden-window-props))
         (warden-buffer (cdr warden-window-props))
         (config
          (r--aget warden-f-alist
                   (window-frame))))

    (when (or config
              prev-buffer)

      (r--aremove warden-w-alist (selected-window))
      ;; revert appearance
      (advice-remove 'dired-readin #'warden-setup-dired-buffer)
      (warden-revert-appearance (or buffer (current-buffer)))
      (warden-revert-appearance warden-buffer)
      (advice-add 'dired-readin :after #'warden-setup-dired-buffer)

      ;; if no more warden frames
      (when (not (or (warden-windows-exists-p)
                     (warden-frame-exists-p)))

        (message "Reverting all buffers")
        ;; remove all hooks and advices
        (advice-remove 'dired-readin #'warden-setup-dired-buffer)
        (remove-hook 'window-configuration-change-hook 'warden-window-check)
        ;; delete and cleanup buffers
        (let ((all-warden-buffers
               (cl-remove-duplicates
                (append
                 warden-preview-buffers
                 warden-parent-buffers
                 warden-visited-buffers
                 (list warden-buffer))
                :test (lambda (x y) (or (null y) (eq x y)))
                )))
          ;; (message (format "all buffers : %s" all-warden-buffers))

          (if warden-cleanup-on-disable
              (mapc 'warden-kill-buffer all-warden-buffers)
              (mapc 'warden-revert-appearance all-warden-buffers)))

        ;; kill preview buffer
        (when (get-buffer "*warden-prev*")
          (kill-buffer (get-buffer "*warden-prev*")))

        (setq warden-f-alist ())
        (setq warden-w-alist ())

        ;; clear variables
        (setq warden-preview-buffers ()
              warden-visited-buffers ()
              warden-parent-buffers ()))

      ;; clear warden-show-details information
      (message "%s" ""))))

(defun warden-revert-appearance (buffer)
  "Revert the `BUFFER' to pre-warden defaults"
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      ;; revert buffer local modes used in warden
      ;; (message (format "reverting : %s" buffer))

      (unless warden-pre-hl-mode
        (hl-line-mode -1))
      (unless warden-pre-arev-mode
        (auto-revert-mode -1))
      (when (derived-mode-p 'dired-mode)
        (unless warden-pre-omit-mode
          (dired-omit-mode -1))
        (setq dired-listing-switches warden-pre-dired-listing)
        (dired-hide-details-mode -1)
        ;; revert warden-mode
        (setq warden-mode nil)
        ;; hide details line at top
        (funcall 'remove-from-invisibility-spec 'dired-hide-details-information)
        (revert-buffer)))))

(defun warden-still-dired ()
  "Enable or disable warden based on current mode"
  (if (derived-mode-p 'dired-mode)
      (warden-mode t)
      (progn
        ;; Try to manage new windows / frames created without killing warden
        (let* ((warden-window-props
                (r--aget warden-w-alist
                         (selected-window)))
               (prev-buffer (car warden-window-props))
               (warden-buffer (cdr warden-window-props))
               (current (current-buffer))
               (buffer-fn (buffer-file-name (current-buffer))))
          (if buffer-fn
              (progn
                (message "File opened, exiting warden")
                (warden-disable)
                (find-file buffer-fn))
              (progn
                (message "Redirecting window to new frame")
                (set-window-buffer nil warden-buffer)
                (when current
                  (display-buffer-other-frame current))))))))

(defun warden-window-check ()
  "Detect when warden-window is no longer part of warden-mode"
  (let* ((windows (window-list))
         (warden-window-props
          (r--aget warden-w-alist
                   (selected-window)))
         (prev-buffer (car warden-window-props))
         (warden-buffer (cdr warden-window-props))
         (warden-windows (r--akeys warden-w-alist))
         (warden-frames (r--akeys warden-f-alist)))
    ;; if all frames and windows are killed, revert buffer settings
    (if (not  (or (warden-windows-exists-p)
                  (warden-frame-exists-p)))
        (progn
          (message "All warden frames have been killed, reverting warden settings and cleaning buffers.")
          (warden-revert))
        ;; when still in warden's window, make sure warden's primary window and buffer are still here.
        (when warden-window-props
          ;; Unless selected window does not have warden buffer
          (unless (and (memq (selected-window) warden-windows)
                       (eq (current-buffer) warden-buffer))
            (remove-hook 'window-configuration-change-hook 'warden-window-check)
            (warden-still-dired))))))

(defun warden-windows-exists-p ()
  "Test if any warden-windows are live."
  (if (delq nil
            (mapcar 'window-live-p
                    (r--akeys warden-w-alist)))
      t
      nil))

(defun warden-frame-exists-p ()
  "Test if any warden-frames are live."
  (if (delq nil
            (mapcar 'frame-live-p
                    (r--akeys warden-f-alist)))
      t
      nil))

(defun warden-kill-buffers-without-window ()
  "Will kill all warden buffers that are not displayed in any window."
  (interactive)
  (cl-loop for buffer in warden-parent-buffers do
           (unless (get-buffer-window buffer t)
             (kill-buffer-if-not-modified buffer)))
  (cl-loop for buffer in warden-preview-buffers do
           (unless (get-buffer-window buffer t)
             (kill-buffer-if-not-modified buffer))))


;; mode line
(defun warden--dir-relative ()
  "Return the topmost directory name in path"
  (let* ((current-name default-directory)
         (parent-name (warden-parent-directory default-directory))
         (relative
          (if (string-equal current-name parent-name)
              current-name
              (file-relative-name current-name parent-name))))
    relative))

(defun warden--ar2ro (AN)
  "translate from arabic number AN to roman number,
   warden--ar2ro returns string of roman numerals."
  (cond
    ((>= AN 10) (concat "X" (warden--ar2ro (- AN 10))))
    ((>= AN 9) (concat "I" (concat "X" (warden--ar2ro (- AN 9)))))
    ((>= AN 5) (concat "V" (warden--ar2ro (- AN 5))))
    ((>= AN 4) (concat "I" (concat "V" (warden--ar2ro (- AN 4)))))
    ((>= AN 1) (concat "I" (warden--ar2ro (- AN 1))))
    ((= AN 0) nil)))

(defun warden-set-modeline ()
  "This is a redefinition of the fn from `dired.el'. This one
properly provides the modeline in dired mode. "
  (when (eq major-mode 'dired-mode)
    (setq mode-name
          (concat
           ;; (if buffer-read-only "<N>" "<I>")
           "warden:"
           (cond ((string-match "^-[^t]*t[^t]*$" dired-actual-switches)
                  "mtime")
                 ((string-match "^-[^c]*c[^c]*$" dired-actual-switches)
                  "ctime")
                 ((string-match "^-[^X]*X[^X]*$" dired-actual-switches)
                  "ext")
                 ((string-match "^-[^S]*S[^S]*$" dired-actual-switches)
                  "size")
                 ((string-match "^-[^SXUt]*$" dired-actual-switches)
                  "name")
                 (t
                  dired-actual-switches))
           (when (string-match "r" dired-actual-switches) " (r)")
           ))
    (with-eval-after-load "diminish"
      (diminish 'warden-mode)
      (diminish 'dired-omit-mode)
      (diminish 'auto-revert-mode))
    (force-mode-line-update)))

(defun warden-setup-dired-buffer ()
  "Setup the dired buffer by removing the header and sorting folders directory first."
  (when (eq (window-frame) warden-frame)
    (save-excursion
      (let ((switches (concat
                       dired-listing-switches
                       warden-sorting-switches))
            (buffer-read-only))
        (forward-line 1)
        ;; check sorting mode and sort with directories first
        (when (and warden-listing-dir-first
                   (not (string-match "[XStU]+" switches)))
          (if (string-match "r" switches)
              (sort-regexp-fields nil "^.*$" "[ ]*." (point) (point-max))
              (sort-regexp-fields t "^.*$" "[ ]*." (point) (point-max))))
        (set-buffer-modified-p nil)))))

;;;###autoload
(defun warden (&optional path)
  "Launch dired in warden-mode."
  (interactive)
  (let* ((file (or path (buffer-file-name)))
         (dir
          (if file
              (file-name-directory file)
              default-directory)))
    (when dir
      (warden-find-file dir))))

(defun warden-to-dired ()
  "Toggle from warden to dired in directory."
  (interactive)
  (let ((dir default-directory))
    (warden-disable)
    (remove-hook 'window-configuration-change-hook 'warden-window-check)
    (dired dir)))

(defun warden-setup ()
  "Setup all associated warden windows."
  (interactive)

  (unless (derived-mode-p 'dired-mode)
    (error "Run it from dired buffer"))

  (warden-define-additional-maps)

  ;; load bookmarks
  (unless bookmark-alist
    (bookmark-maybe-load-default-file))

  (require 'dired-x)

  (run-hooks 'warden-mode-load-hook)

  ;; store previous settings
  (unless warden-pre-saved
    (setq warden-pre-hl-mode hl-line-mode)
    (setq warden-pre-arev-mode auto-revert-mode)
    (setq warden-pre-omit-mode dired-omit-mode)
    (setq warden-pre-dired-listing dired-listing-switches)
    (setq warden-pre-saved t))

  ;; save window-config for frame unless already
  ;; specified from running `warden'
  (warden-save-window-settings)

  ;; warden specific objects
  (setq warden-buffer (current-buffer))
  (setq warden-window (get-buffer-window (current-buffer)))
  (setq warden-frame (window-frame warden-window))

  (r--aput warden-w-alist
           (selected-window)
           (cons
            (car-safe (r--aget warden-w-alist (selected-window)))
            (current-buffer)))

  (setq warden-preview-window nil)

  ;; hide groups, show human readable file sizes
  (setq dired-listing-switches warden-listing-switches)
  (dired-hide-details-mode -1)
  (delete-other-windows)

  ;; consider removing
  (auto-revert-mode)

  ;; set hl-line-mode for warden usage
  ;;;; (hl-line-mode t)

  ;; truncate lines for primary window
  (setq truncate-lines t)

  ;; clear out everything
  (add-to-list 'warden-visited-buffers warden-buffer)

  ;; hide details line at top - show symlink targets
  (funcall 'add-to-invisibility-spec 'dired-hide-details-information)
  (make-local-variable 'dired-hide-symlink-targets)
  (setq dired-hide-details-hide-symlink-targets nil)

  (warden-sort t)
  (warden-show-flags)
  (warden-omit)
  (warden-hide-dotfiles)
  (warden-setup-parents)
  (warden-setup-preview)

  ;; scroll back to left in case new windows affected primary buffer
  (set-window-hscroll warden-window 0)

  ;; reset subdir optiona
  (setq warden-subdir-p nil)

  (warden-show-details)
  (warden-set-modeline))

;;;###autoload
(define-minor-mode warden-mode
    "A convienent way to look up file contents in other window while browsing directory in dired"
  :init-value nil
  :lighter " warden"
  :keymap 'warden-mode-map
  :group 'warden
  ;; :after-hook 'warden-mode-hook
  (if warden-mode
      (progn
        (advice-add
         'dired-readin :after #'warden-setup-dired-buffer)
        (warden-setup)
        (add-hook
         'window-configuration-change-hook
         'warden-window-check))
      (warden-revert)))

(provide 'warden)

;;; warden.el ends here
