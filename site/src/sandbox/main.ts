import "purr/fonts.css";
import "purr/styles.css";
import "purr/shell.css";
import "../styles/code.css";
import { mount } from "svelte";
import { loadKanonSyntax } from "../highlight/kanon";
import { startTheme } from "../lib/theme";
import Sandbox from "./Sandbox.svelte";

startTheme();
// the editor's states are made with the highlighting, so it loads first (it is quick)
const syntax = await loadKanonSyntax();
mount(Sandbox, { target: document.getElementById("app")!, props: { syntax } });
