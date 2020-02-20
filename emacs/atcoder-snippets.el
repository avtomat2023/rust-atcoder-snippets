(require 'json)

(require 'dash)
(require 'ht)

(defun atcoder-snippets--to-hashset (string-list)
  (ht-from-alist (--map `(,it . t) string-list)))

(defvar atcoder-snippets-repository-path nil
  "Path of atcoder-snippets repository's root directory.
Clone https://github.com/yoshrc/rust-atcoder-snippets and set the path of the repository.")

(defvar atcoder-snippets-json-path (concat (getenv "HOME") "/.emacs.d/atcoder-snippets.json")
  "Path of the json file generated from the repository.")

(defvar atcoder-snippets-acc-template-path nil
  "Path of the Rust template file for atcoder-cli.")

(defun atcoder-snippets--read-json ()
  (let ((json-key-type 'string)
        (json-object-type 'hash-table)
        (json-array-type 'list))
    (json-read-file atcoder-snippets-json-path)))

(defvar atcoder-snippets--snippets (atcoder-snippets--read-json)
  "Snippet read from json file.")

(defun atcoder-snippets--names-sorted-alphabetically ()
  (sort (ht-keys atcoder-snippets--snippets) 'string<))

(defun atcoder-snippets--dep-graph ()
  "Hashtable: name (string) -> dependencies (list of string)"
  (ht-from-alist
   (ht-map (lambda (key value) (cons key (ht-get value "dependencies")))
           atcoder-snippets--snippets)))

(defun atcoder-snippets--calc-dep ()
  (let ((graph (atcoder-snippets--dep-graph))
        (visited (ht-create))
        (result nil))
    ;; reverse names to sort result as alphabetical as possible
    (dolist (name (reverse (atcoder-snippets--names-sorted-alphabetically)))
      (setq result (atcoder-snippets--calc-dep-sub name graph visited result)))
    result))

(defun atcoder-snippets--calc-dep-sub (name graph visited acc)
  ;; topological sort by depth-first search
  (if (ht-contains? visited name)
      acc
    (ht-set! visited name t)
    (dolist (next (ht-get graph name))
      (setq acc (atcoder-snippets--calc-dep-sub next graph visited acc)))
    (cons name acc)))

(defvar atcoder-snippets--order (atcoder-snippets--calc-dep)
  "Snippet names sorted topologically by dependencies.
'(\"s1\" \"s2\" \"s3\") means s1 may depend on s2 and s3, and s2 may depend on s3.")

(defun atcoder-snippets--move-before-pattern (pattern)
  (goto-char (point-min))
  (while (let ((index (string-match-p pattern (thing-at-point 'line))))
           (and (/= (point) (point-max)) (or (not index) (/= index 0))))
    (forward-line)))

(defun atcoder-snippets--move-before-snippet (name)
  (atcoder-snippets--move-before-pattern (concat " *// *SNIPPET +" name)))

(defun atcoder-snippets--move-before-end-snippets ()
  (atcoder-snippets--move-before-pattern " *// *END +SNIPPETS"))

(defun atcoder-snippets--insert-snippet-before (name before)
  (save-excursion
    (cond (before (atcoder-snippets--move-before-snippet before))
          (t (atcoder-snippets--move-before-end-snippets)))
    (insert (format "// SNIPPET %s\n" name))
    (insert (ht-get (ht-get atcoder-snippets--snippets name) "text"))
    (insert "\n")))

(defun atcoder-snippets--linearize-by-dep (names-ht)
  (let ((result nil))
    (dolist (name atcoder-snippets--order)
      (when (ht-contains? names-ht name)
        (push name result)))
    (when (/= (length result) (ht-size names-ht))
      (error (format "Contains invalid snippet name: %S" (ht-keys names-ht))))
    (reverse result)))

(defun atcoder-snippets--append-deps (name)
  (let* ((graph (atcoder-snippets--dep-graph))
         (visited (ht-create))
         (names-unsorted (atcoder-snippets--calc-dep-sub name graph visited nil))
         (names-ht (atcoder-snippets--to-hashset names-unsorted)))
    (atcoder-snippets--linearize-by-dep names-ht)))

(defun atcoder-snippets--inserted-snippets ()
  (save-excursion
    (let ((names nil))
      (goto-char (point-min))
      (while (/= (point) (point-max))
        (let* ((line (thing-at-point 'line))
               (index (string-match " *// *SNIPPET +\\([-_a-zA-Z0-9]+\\)" line)))
          (when (and index (= index 0))
            (push (match-string 1 line) names)))
        (forward-line))
      names)))

(defun atcoder-snippets--merge-name-list (names1 names2)
  (let* ((names1-ht (atcoder-snippets--to-hashset names1))
         (names2-ht (atcoder-snippets--to-hashset names2))
         (merged (ht-merge names1-ht names2-ht)))
    (atcoder-snippets--linearize-by-dep merged)))

(defun atcoder-snippets--exclude-name-list (names excludings)
  (let ((result (atcoder-snippets--to-hashset names)))
    (dolist (name excludings)
      (ht-remove! result name))
    (atcoder-snippets--linearize-by-dep result)))

;; TODO: This function takes O(n^2) for `order's length.
;;       Moving cursor backward improves the complexity.
(defun atcoder-snippets--insert-snippets-by-order (names order)
  (when names
    (cond
     ((equal (car names) (cadr order))
      (atcoder-snippets--insert-snippet-before (car names) (car order))
      (atcoder-snippets--insert-snippets-by-order (cdr names) (cdr order)))
     (t (atcoder-snippets--insert-snippets-by-order names (cdr order))))))

(defun atcoder-snippets-insert (name)
  (interactive "sSnippet name: ")
  (let* ((json (json-read-file atcoder-snippets-json-path))
         (snippet (alist-get name json nil nil 'string=)))
    (when (not snippet)
      (error (format "Not snippet named %s" name)))
    (let* ((names (atcoder-snippets--append-deps name))
           (inserteds (atcoder-snippets--inserted-snippets))
           (order (atcoder-snippets--merge-name-list names inserteds))
           (insertings (atcoder-snippets--exclude-name-list names inserteds)))
      (save-excursion (atcoder-snippets--insert-snippets-by-order insertings (cons nil order))))))

(defun atcoder-snippets--write-acc-template ()
  (with-temp-buffer
    (insert "// END SNIPPETS

fn main() {
    ")
    (atcoder-snippets-insert "read")
    (atcoder-snippets-insert "dbg")
    (write-region nil nil atcoder-snippets-acc-template-path)))

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
      (error "Snippet processing failed: see *atcoder-snippets output* buffer")))
  (setq atcoder-snippets--snippets (atcoder-snippets--read-json))
  (setq atcoder-snippets--order (atcoder-snippets--calc-dep))
  (when atcoder-snippets-acc-template-path
    (atcoder-snippets--write-acc-template)))

(provide 'atcoder-snippets)
