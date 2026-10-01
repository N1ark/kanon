import "purr/fonts.css";
import "purr/styles.css";
import "../styles/code.css";
import { mount } from "svelte";
import { startTheme } from "../lib/theme";
import Tutorial from "./Tutorial.svelte";

startTheme();
mount(Tutorial, { target: document.getElementById("app")! });
