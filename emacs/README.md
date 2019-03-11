# atcoder-snippets for Emacs

## Requirements

- [cargo-snippet](https://github.com/hatoo/cargo-snippet)
- [rust-mode](https://github.com/rust-lang/rust-mode)
- [yasnippet](https://github.com/joaotavora/yasnippet)

## How to use

1. Clone this repository.
2. Add the path of `emacs/bin` directory under the repository to `$PATH` by editing the login commands file like `~/.profile`.
3. Log out from your OS and log in again.
4. Execute:
   ```
   (push "/path/to/atcoder-snippets/emacs" load-path)
   (require 'atcoder-snippets)
   (setq atcoder-snippets-repository-path "/path/to/atcoder-snippets")

   (require 'yasnippet)
   (atcoder-snippets-reload)
   ```
5. Open a rust file and type a snippet name like `read`. Then `M-x yas-expand`.
