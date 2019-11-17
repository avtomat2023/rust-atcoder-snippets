# Rust AtCoder Snippets

Utility snippets for AtCoder, easily copy-and-pastable on Emacs

[Documentation](https://yoshrc.github.io/rust-atcoder-snippets/)

## Usage for Emacs

1. Install [dash.el](https://github.com/magnars/dash.el) and [ht.el](https://github.com/Wilfred/ht.el).
1. Clone this repository.
1. Add the path of `bin` directory under the repository to `$PATH` by editing the login commands file like `~/.profile`.
1. Log out from your OS and log in again.
1. Execute `atcoder-snippets /path/to/repository > ~/.emacs.d/atcoder-snippets.json` in a shell.
1. Evaluate the folloing S-expressions in your Emacs:
   ```
   (push "/path/to/atcoder-snippets/emacs" load-path)
   (require 'atcoder-snippets)
   (setq atcoder-snippets-repository-path "/path/to/repository")
   ```
1. Open a rust file.
1. Add a line `// END SNIPPETS` at the beginning of the file.
1. Hit `M-x atcoder-snippets-insert`. For example, insert `read` or `dbg`.

### Optional: Use Helm Completion

If you'd like to use Helm completion when inserting, evaluate `(require 'atcoder-snippets-helm)`. Then you can use `M-x atcoder-snippet-helm-insert`.

### Optional: Generate template for atcoder-cli

Set `atcoder-snippet-acc-template-path` as the path of template source code for Rust config of atcoder-cli. Then `M-x atcoder-snippets-reload` generates the template code containing `read` and `dbg` snippets.
