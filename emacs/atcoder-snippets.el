(require 'json)

(defvar atcoder-snippets-repository-path nil
  "Path of atcoder-snippets repository's root directory.
Clone https://github.com/yoshrc/rust-atcoder-snippets and set the path of the repository.")

(defvar atcoder-snippets-json-path (concat (getenv "HOME") "/.emacs.d/atcoder-snippets.json")
  "Path of the json file generated from the repository.")

(defun atcoder-snippets-reload ()
  (interactive)
  (when (not atcoder-snippets-repository-path)
    (error "Set `atcoder-snippets-repository-path`"))
  (let ((cmd (concat "atcoder-snippets "
                     (shell-quote-argument atcoder-snippets-repository-path)
                     " > "
                     (shell-quote-argument atcoder-snippets-json-path))))
    (when (/= (call-process "sh" nil '("*atcoder-snippets output*" t) nil
                            "-c" cmd)
              0)
      (error "Snippet processing failed: see *atcoder-snippet output* buffer"))))

(defun atcoder-snippets-names ()
  (let ((json-key-type 'string))
    (sort (-map 'car (json-read-file atcoder-snippets-json-path)) 'string<)))

(defun atcoder-snippets-insert (name)
  (interactive "sSnippet name: ")
  (let* ((json (json-read-file atcoder-snippets-json-path))
         (snippet (alist-get name json nil nil 'string=)))
    (cond
     (snippet
      (let ((text (alist-get 'text snippet))
            (deps (alist-get 'dependencies snippet)))
        (save-excursion
          (goto-char (point-min))
          (let ((flag t))
            (while (and flag (/= (point) (point-max)))
              (if (eq (string-match-p " *// *END *SNIPPETS" (thing-at-point 'line)) 0)
                  (setq flag nil)
                (forward-line))))
          (when (= (point) (point-max))
            (goto-char (point-min)))
          (insert (format "// SNIPPET %s\n" name))
          (insert text)))))))

(defun atcoder-snippets-list-inserted-snippets ()
  (save-excursion
    (let ((snippets (make-hash-table :test 'equal)))
      (goto-char (point-min))
      (while (/= (point) (point-max))
        (when (eq (string-match " *// *SNIPPET *\\([-_a-zA-Z0-9]+\\)" (thing-at-point 'line)) 0)
          (puthash (match-string 1 (thing-at-point 'line)) t snippets))
        (forward-line))
      snippets)))

(provide 'atcoder-snippets)
