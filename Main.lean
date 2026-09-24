import VersoSlides

import QIC891.Lecture1 -- so `%doc` below finds the module
import QIC891.Lecture2
import QIC891.Lecture3
import QIC891.Lecture4

open VersoSlides
open Verso.Doc (Part)
open System (FilePath)

def myExtraCss : CssFile where
  filename := "custom.css"
  contents := ⟨include_str "QIC891/_assets/custom.css"⟩

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
  ("lecture2", (%doc QIC891.Lecture2), "_slides/lecture2"),
  ("lecture3", (%doc QIC891.Lecture3), "_slides/lecture3"),
  ("lecture4", (%doc QIC891.Lecture4), "_slides/lecture4"),
]

/-- With no args, builds every deck; otherwise only the named ones
(e.g. `lake exe qic891 lecture1 lecture3`). -/
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
