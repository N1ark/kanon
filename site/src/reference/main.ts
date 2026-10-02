import "purr/fonts.css";
import "purr/styles.css";
import "../styles/code.css";
import { mount } from "svelte";
import { startTheme } from "../lib/theme";
import Reference from "./Reference.svelte";

startTheme();
mount(Reference, { target: document.getElementById("app")! });
