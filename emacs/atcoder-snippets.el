(defvar atcoder-snippets-repository-path)

(defvar atcoder-snippets-dir (expand-file-name "~/.emacs.d/snippets/rust-mode"))

(defun atcoder-snippets-reload ()
  (interactive)
  (let ((cmd (concat "cargo snippet -t vscode | atcoder-snippets-deploy-emacs "
                     (shell-quote-argument atcoder-snippets-dir)))
        (default-directory atcoder-snippets-repository-path))
    (when (/= (call-process "sh" nil '("*atcoder-snippet output*" t) nil
                            "-c" cmd)
              0)
      (error "Snippet deployment failed")))
  (yas-reload-all))
