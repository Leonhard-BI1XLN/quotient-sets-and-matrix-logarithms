import Std

/-!
Independent verification of the two finite exponent counts in the cross-block
lemma. The general group argument that eliminates the two axes and restricts
the involution case to an empty or singleton intersection is external to this file.
-/

namespace QuotientPairWeights

private def bits : List Int := [0, 1]
private def signs : List Int := [-1, 0, 1]

private def count (items : List Int) (test : Int → Bool) : Int :=
  Int.ofNat (items.filter test).length

/-- Count matches between the two opposite-direction right quotient lists. -/
private def rightMatches (exponents : List Int) (table : Int → Int → Bool) : Int :=
  (exponents.map (fun a => count exponents (table a))).sum

/-- Count matches between the two four-entry lists of left quotients. -/
private def leftMatches (table : Int → Int → Bool) : Int :=
  (bits.map (fun p => (bits.map (fun p' => (bits.map (fun q =>
    count bits (fun q' => table (p' - p) (q - q')))).sum)).sum)).sum

/-- Each mask permits an arbitrary subset of the four corners and the origin.
The group argument proves that the remaining four entries are false. -/
private def noninvolutionTable (mask : Fin 32) (a b : Int) : Bool :=
  match a, b with
  | -1, -1 => mask.val.testBit 0
  | -1,  1 => mask.val.testBit 1
  |  1, -1 => mask.val.testBit 2
  |  1,  1 => mask.val.testBit 3
  |  0,  0 => mask.val.testBit 4
  | _, _   => false

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem noninvolution_weight_identity :
    ∀ mask : Fin 32,
      (6 - rightMatches signs (noninvolutionTable mask)) -
      (8 - leftMatches (noninvolutionTable mask)) =
      -2 + (if noninvolutionTable mask 0 0 then 3 else 0) := by decide

/-- Codes 0,...,3 pick a unique residue pair modulo 2. Code 4 picks none. -/
private def involutionTable (choice : Fin 5) (a b : Int) : Bool :=
  decide ((choice.val : Int) = 2 * (a % 2) + (b % 2))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem involution_weight_identity :
    ∀ choice : Fin 5,
      rightMatches bits (involutionTable choice) =
          (if choice.val = 4 then 0 else 1) ∧
      leftMatches (involutionTable choice) =
          (if choice.val = 4 then 0 else 4) ∧
      (4 - rightMatches bits (involutionTable choice)) -
      (8 - leftMatches (involutionTable choice)) =
          (if choice.val = 4 then -4 else -1) := by decide

#print axioms noninvolution_weight_identity
#print axioms involution_weight_identity

end QuotientPairWeights
