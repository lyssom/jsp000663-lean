import JSP000663

/-!
Axiom audit script. Uses `#print axioms` to list every axiom each main theorem
depends on. Any axiom outside `propext`, `Quot.sound`, `Classical.choice` would
indicate a leaked assumption.

Run with `lake env lean scripts/check_axioms.lean`. -/

section Basic

#print axioms JSP000663.erdos_newman_1977
#print axioms JSP000663.coverWitness_twoCover
#print axioms JSP000663.coverWitness_card_le
#print axioms JSP000663.split_sum
#print axioms JSP000663.coverWitness
#print axioms JSP000663.twoCover
#print axioms JSP000663.sumset

end Basic

section Tight

#print axioms JSP000663.coverWitness_twoCover_subset
#print axioms JSP000663.coverWitness_subset_of_small
#print axioms JSP000663.erdos_newman_ABS09

end Tight