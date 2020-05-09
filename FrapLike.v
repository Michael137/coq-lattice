(*Module FrapLike.*)

Ltac propositional := intuition idtac.

Ltac cases E :=
  ((repeat match type of E with
      | _ \/ _ => destruct E as [E | E]
      end)
  || (is_var E; destruct E)
  || match type of E with
     | {_} + {_} => destruct E
     | _ => let Heq := fresh "Heq" in destruct E eqn:Heq
     end);
  repeat match goal with
         | [ H: _ = left _ |- _ ] => clear H
         | [ H: _ = right _ |- _ ] => clear H
         end.

Ltac invert' H := inversion H; clear H; subst.

Ltac invertN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => invert' H
              | S ?n' => invertN n'
            end
        | _ => intro; invertN n
      end
  end.

Ltac invert e := invertN e || invert' e.

Ltac equality := intuition congruence.

(*End FrapLike.*)
