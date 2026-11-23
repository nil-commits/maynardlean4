/-
MaynardDock — Axiom & Grounding Audit.

Prints the axioms of every top-level MaynardDock theorem (both H = 600 and H = 246).
Expected axiom set: `{propext, Classical.choice, Quot.sound}` only.
-/
import MaynardDock.Capstone
import MaynardDock.Capstone246

#print axioms MaynardDock.maynardBombieriVinogradov
#print axioms MaynardDock.unconditional_prime_gap_le_600
#print axioms MaynardDock.bounded_prime_gaps_unconditional
#print axioms MaynardDock.frequently_consecutive_prime_gap_le_600
#print axioms MaynardDock.unconditional_prime_gap_le_246
#print axioms MaynardDock.bounded_prime_gaps_246_unconditional
#print axioms MaynardDock.frequently_consecutive_prime_gap_le_246
#print axioms MaynardDock.unconditional_nth_prime_gap_le_246
