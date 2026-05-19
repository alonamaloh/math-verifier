# Emacs integration

Emacs' `compilation-mode` already knows the canonical `FILE:LINE:COL:`
format, so errors are clickable out of the box.

## One-time setup

Add this to your `init.el` (or any startup file). The `dir-locals`
recipe further down restricts the behavior to this project so it doesn't
follow you into unrelated buffers.

```elisp
;; A `math-mode` for `.math` files — minimal, just so Emacs has a hook
;; to hang the auto-rebuild onto. If you want syntax highlighting,
;; derive from `prog-mode` and add font-lock rules.
(define-derived-mode math-mode prog-mode "Math"
  "Major mode for the math proof assistant's .math files."
  (setq-local comment-start "-- ")
  (setq-local comment-end ""))

(add-to-list 'auto-mode-alist '("\\.math\\'" . math-mode))

;; Rebuild on save.
(defvar math-build-command "make -j 16 library")

(defun math-rebuild-on-save ()
  "Run `compile' with the library build command. Bound to after-save
in `math-mode' buffers via dir-locals."
  (let ((default-directory (math--project-root)))
    (when default-directory
      (let ((compilation-ask-about-save nil)
            (compilation-save-buffers-predicate (lambda () nil)))
        (compile math-build-command)))))

(defun math--project-root ()
  "Find the math project root from the current buffer (the directory
containing the `Makefile` and `library/`)."
  (locate-dominating-file
   (or buffer-file-name default-directory)
   (lambda (dir)
     (and (file-exists-p (expand-file-name "Makefile" dir))
          (file-directory-p (expand-file-name "library" dir))))))
```

## Per-project enablement

In the math repo root, create `.dir-locals.el`:

```elisp
((math-mode . ((eval . (add-hook 'after-save-hook
                                  #'math-rebuild-on-save
                                  nil 'local)))))
```

Now opening any `.math` file in the repo turns on save-triggered
recompilation. Errors land in the `*compilation*` buffer; `M-x
next-error` (`C-x \`` by default) jumps to each one.

## Make the breadcrumb visible

The first line of each error is `FILE:LINE:COL: kind: short message`.
The indented lines below it are the breadcrumb stack with context and
goal at each level. `compilation-mode` collapses them by default; to
keep them visible, set:

```elisp
(setq compilation-context-lines nil)  ;; show full message text
(setq compilation-scroll-output 'first-error)
```

When you `M-x next-error` to a failure point, glance at the
`*compilation*` buffer to see the context/goal block printed under the
error line.

## Optional: a popup-style hover

If you want the context/goal next to the cursor in the editor instead
of in the `*compilation*` buffer, use `flymake` with a custom backend.
Sketch:

```elisp
(defun math-flymake-backend (report-fn &rest _args)
  "Run `make -j 16 library` and feed diagnostics back to flymake."
  ;; left as an exercise — parse stdout/stderr of `make`, regex the
  ;; FILE:LINE:COL: prefix, surface each as a flymake diagnostic with
  ;; the breadcrumb block as the message body
  )
```

For day-to-day use the `compile`-on-save flow plus `next-error` is
already comfortable; flymake is the polish step.
