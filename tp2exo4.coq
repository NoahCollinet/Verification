Section Peano.
Parameter N : Set.
Parameter o : N.
Parameter s : N -> N.
Parameters plus mult : N -> N -> N.
Variables x y : N.
Axiom ax1 : ~((s x) = o).
Axiom ax2 : exists z, ~(x = o) -> (s z) = x.
Axiom ax3 : (s x) = (s y) -> x = y.
Axiom ax4 : (plus x o) = x.
Axiom ax5 : (plus x (s y)) = s (plus x y).
Axiom ax6 : (mult x o) = o.
Axiom ax7 : (mult x (s y)) = (plus (mult x y) x).
End Peano.

Lemma peano_ex1 : (plus (s o) (s (s o))) = (s (s (s o))).
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.
Qed.

Lemma peano_ex2 : (plus (s (s o)) (s (s o))) = (s (s (s (s o)))).
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.
Qed.


Lemma peano_ex3 : (mult (s (s o)) (s (s o))) = (s (s (s (s o)))).
rewrite ax7.
rewrite ax5.
rewrite ax5.
rewrite ax4.
rewrite ax7.
rewrite ax6.
rewrite ax5.
rewrite ax5.
rewrite ax4.
reflexivity.
Qed.
