/-
Copyright (c) OpenAI.
Released under Apache 2.0 license.
Source: https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/IntegralMeans/Model.lean
Imports narrowed and unrelated integral-means definitions removed.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Disk and univalence definitions
-/

namespace OAI

noncomputable section
namespace Brennan

def disk : Set ℂ := Metric.ball 0 1

def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ Set.InjOn f U

def Schlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

end Brennan

end

end OAI
