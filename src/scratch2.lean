import tactic
import data.set.basic
import order.filter.bases 
import data.finset.basic 
import data.set.finite 

example (X : Type*) (S : set X) (h_finite : S.finite) : 
∃ (T : set X), ∃ (x : X), ∃ (h_T_finite : T.finite), (h_T_finite.to_finset.card = h_finite.to_finset.card - 1) ∧ (S = (T ∪ ({x} : set X))) := 
sorry

