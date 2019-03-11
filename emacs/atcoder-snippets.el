(defvar atcoder-snippets-repository-path nil
  "Path of atcoder-snippets repository.
Clone https://github.com/yoshrc/rust-atcoder-snippets and set the path of the repository.")

(defvar atcoder-snippets-dir (expand-file-name "~/.emacs.d/snippets/rust-mode")
  "The directory where snippet files get deployed in.")

(defun atcoder-snippets-reload ()
  (interactive)
  (when (not atcoder-snippets-repository-path)
    (error "Set `atcoder-snippets-repository-path`"))
  (let ((cmd (concat "cargo snippet -t vscode | atcoder-snippets-deploy-emacs "
                     (shell-quote-argument atcoder-snippets-dir)))
        (default-directory atcoder-snippets-repository-path))
    (when (/= (call-process "sh" nil '("*atcoder-snippet output*" t) nil
                            "-c" cmd)
              0)
      (error "Snippet deployment failed: see *atcoder-snippet output* buffer")))
  (yas-reload-all))

(provide 'atcoder-snippets)
