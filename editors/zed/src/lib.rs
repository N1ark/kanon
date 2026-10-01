//! The Zed extension of Kanon: the language itself is declarative (`extension.toml`,
//! `languages/kanon/`); this only tells Zed how to start the language server,
//! `kanon lsp`, which is not bundled but found on the user's machine.

use zed_extension_api::{self as zed, settings::LspSettings, LanguageServerId, Result, Worktree};

/// The key of the server in `extension.toml` and in the `lsp` settings.
const SERVER: &str = "kanon";

struct KanonExtension;

impl zed::Extension for KanonExtension {
    fn new() -> Self {
        KanonExtension
    }

    fn language_server_command(
        &mut self,
        _language_server_id: &LanguageServerId,
        worktree: &Worktree,
    ) -> Result<zed::Command> {
        // `lsp.kanon.binary` wins, then the `kanon` of the worktree's shell, so
        // that the one of an opam switch or of a direnv is found.
        let binary = LspSettings::for_worktree(SERVER, worktree)
            .ok()
            .and_then(|settings| settings.binary);
        let (path, arguments, extra_env) = match binary {
            Some(b) => (b.path, b.arguments, b.env),
            None => (None, None, None),
        };
        let command = path.or_else(|| worktree.which("kanon")).ok_or_else(|| {
            "kanon was not found on the PATH: install it (`opam pin add kanon \
             https://github.com/N1ark/kanon.git`, or `dune install` from a checkout), \
             or set `lsp.kanon.binary.path` in Zed's settings"
                .to_string()
        })?;
        // The shell's environment, as opam needs it (OCAMLPATH, ...); the
        // variables of the settings override it.
        let mut env = worktree.shell_env();
        for (name, value) in extra_env.into_iter().flatten() {
            env.retain(|(n, _)| *n != name);
            env.push((name, value));
        }
        Ok(zed::Command {
            command,
            args: arguments.unwrap_or_else(|| vec!["lsp".to_string()]),
            env,
        })
    }

    fn language_server_initialization_options(
        &mut self,
        _language_server_id: &LanguageServerId,
        worktree: &Worktree,
    ) -> Result<Option<zed::serde_json::Value>> {
        Ok(LspSettings::for_worktree(SERVER, worktree)
            .ok()
            .and_then(|settings| settings.initialization_options))
    }

    fn language_server_workspace_configuration(
        &mut self,
        _language_server_id: &LanguageServerId,
        worktree: &Worktree,
    ) -> Result<Option<zed::serde_json::Value>> {
        Ok(LspSettings::for_worktree(SERVER, worktree)
            .ok()
            .and_then(|settings| settings.settings))
    }
}

zed::register_extension!(KanonExtension);
