# Math480GroupProject

A structural template for formalizing Vizing's Theorem in Lean4 with Mathlib.

What This Is
This repository provides a proof outline and scaffolding for Vizing's Theorem, which states that any simple graph can be edge-colored using at most Δ + 1 colors (where Δ is the maximum degree).

The code includes:
  *Proper type definitions for edge colorings
  *Correct proof strategy (induction on edge count)
  *Key case analysis structure
  *All necessary imports and setup
  *Actual proofs (intentionally left as sorry)

What This Isn't:
  *This is not a complete formalization. It's a template that captures the essential structure of Vizing's proof for others to complete.

Who This Is For:
  *Researchers wanting to formalize graph theory results
  *Students learning Lean4 who want a challenging but structured project
  *Anyone interested in contributing to formalized combinatorics
  *Prerequisites: Familiarity with Lean4, Mathlib, and ideally some knowledge of Vizing's theorem.

Getting Started:
  *Clone the repository
  *Look for sorry statements throughout the code
  *Fill in the missing definitions and proofs
  *The comments provide guidance on what each piece should accomplish
  *The most challenging part will be implementing the alternating path argument in the case where no color is immediately available for a new edge.

Link to project demonstration slides: [Slides](https://docs.google.com/presentation/d/1N_uLORDeTjfh0iEFjjXzPVdvG6R7htz3ZhWcDOgj9-A/edit?usp=sharing)
