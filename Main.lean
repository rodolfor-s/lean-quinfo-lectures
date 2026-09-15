import VersoSlides

import QIC891.Lecture1 -- so `%doc` below finds the module

open VersoSlides
open Verso.Doc (Part)
open System (FilePath)

def myExtraCss : CssFile where
  filename := "custom.css"
  contents := ⟨":root {
                  --r-main-font-size: 32px;
                  --r-accent: #e7ad52;
                  --r-heading-color: var(--r-accent);
                  --r-link-color: #1976d2;
                }
                .reveal .slides section {
                  overflow-y: auto;
                  max-height: 100%;
                }
                .reveal :is(p, li, td, th, blockquote) code {
                  background-color: #c9c9c9;
                  color: #1a1a1a;
                  font-family: var(--r-code-font, monospace);
                  padding: 0.05em 0.25em;
                  margin: 0 0.15em;
                  border-radius: 4px;
                }
                .reveal .controls {
                  color: var(--r-accent);
                }
                .reveal .progress {
                  color: var(--r-accent);
                }
                /* Bigger fontsize for ```code blocks```.
                   `!important` is needed because custom.css loads
                   before lib/slides-highlight.css and lib/panel.css, whose
                   rules share the same selector specificity.
                   `.info-panel`
                   is the hover-info side panel shown next to `-panel` Lean
                   blocks. It's a separate element from the code box. */
                .reveal code.hl.lean.block,
                .reveal pre:not(.code-with-panel pre),
                .reveal .info-panel {
                  font-size: 1.0em !important;
                }
              "⟩

def buildSlideDeck
(docVal : Part Slides) (outputDirVal : FilePath) : IO UInt32 :=
  slidesMain
    (config := {
      theme := "night",
      slideNumber := true,
      transition := "slide",
      highlightTheme := .solarizedDark,
      outputDir := outputDirVal,
      width := 1600,
      height := 900,
      extraCss := #[myExtraCss] })
    (doc := docVal)

/-- Name each deck so it can be selected individually from the command line. -/
def deckSpecs : List (String × Part Slides × FilePath) := [
  ("lecture1", (%doc QIC891.Lecture1), "_slides/lecture1"),
]

/-- With no args, builds every deck; otherwise only the named ones
(e.g. `lake exe qic891 lecture1`). -/
def main (args : List String) : IO UInt32 := do
  let deckNames := deckSpecs.map Prod.fst
  let unknown := args.filter (· ∉ deckNames) -- catch typos before build
  if !unknown.isEmpty then
    IO.eprintln s!"Unknown slide deck(s): {String.intercalate ", " unknown}"
    IO.eprintln s!"Available: {String.intercalate ", " deckNames}"
    return 1
  -- Empty args is to "build everything"
  let selected := if args.isEmpty then deckSpecs else deckSpecs.filter (args.contains ·.1)
  for (name, docVal, outputDirVal) in selected do
    IO.println s!"Building {name}..."
    let rc ← buildSlideDeck docVal outputDirVal
    if rc != 0 then return rc -- stop at the first failing deck
  return 0
