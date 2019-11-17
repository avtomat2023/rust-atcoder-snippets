(require 'atcoder-snippets)
(require 'helm)

(require 'dash)
(require 'ht)

(defun atcoder-snippets-helm-insert ()
  (interactive)
  (let* ((names (atcoder-snippets--names-sorted-alphabetically))
         (inserteds (atcoder-snippets--to-hashset (atcoder-snippets--inserted-snippets)))
         (candidates (--filter (not (ht-contains? inserteds it)) names)))
    (if (not candidates)
        (message "All snippets are already inserted.")
      (let ((source `((name . "Snippets not yet pasted")
                      (candidates . ,candidates)
                      (action . atcoder-snippets-insert))))
        (helm :sources '(source) :buffer "*Helm atcoder-snippets*")))))

(provide 'atcoder-snippets-helm)
