import "purr/fonts.css";
import "purr/styles.css";
import "../styles/code.css";
import { mount } from "svelte";
import { startTheme } from "../lib/theme";
import Proving from "./Proving.svelte";

startTheme();
mount(Proving, { target: document.getElementById("app")! });
