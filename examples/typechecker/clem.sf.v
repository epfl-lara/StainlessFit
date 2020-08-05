(* Type Checking File clem.sf: Success *)

Require Export SystemFR.Derivation.


(* Base context with primitives *)
Definition Γ : context :=
  (* NatToBoolBinOp *)
  (0, (T_arrow T_nat (T_arrow T_nat T_bool))) (* == *)
  ::(1, (T_arrow T_nat (T_arrow T_nat T_bool))) (* != *)
  ::(2, (T_arrow T_nat (T_arrow T_nat T_bool))) (* <= *)
  ::(3, (T_arrow T_nat (T_arrow T_nat T_bool))) (* >= *)
  ::(4, (T_arrow T_nat (T_arrow T_nat T_bool))) (* < *)
  ::(5, (T_arrow T_nat (T_arrow T_nat T_bool))) (* > *)
  (* NatToNatBinOp *)
  ::(6, (T_arrow T_nat (T_arrow T_nat T_nat))) (* + *)
  ::(7, (T_arrow T_nat (T_arrow T_nat T_nat))) (* - *)
  ::(8, (T_arrow T_nat (T_arrow T_nat T_nat))) (* * *)
  ::(9, (T_arrow T_nat (T_arrow T_nat T_nat))) (* | *)
  (* BoolToBoolBinOp *)
  ::(10, (T_arrow T_bool (T_arrow T_bool T_bool))) (* && *)
  ::(11, (T_arrow T_bool (T_arrow T_bool T_bool))) (* || *)
  (* BoolToBoolUnOp *)
  ::(12, (T_arrow T_bool T_bool)) (* ~ *)
  ::nil.
    
Definition ds : (list derivation) := 
((N (TJ J_If nil Γ (ite (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) (app (app (fvar 6 term_var) (succ zero)) ((succ zero))) (app (app (fvar 6 term_var) (succ (succ zero))) ((succ (succ (succ (succ (succ (succ (succ (succ (succ zero)))))))))))) T_nat)
  ((N (TJ CheckReflexive nil Γ (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) T_bool)
    ((N (TJ J_App nil Γ (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) T_bool)
      ((N (TJ J_App nil Γ (app (fvar 5 term_var) (succ (succ (succ zero)))) (T_arrow T_nat T_bool))
        ((N (TJ J_Var nil Γ (fvar 5 term_var) (T_arrow T_nat (T_arrow T_nat T_bool))) nil)
        ::(N (TJ J_Nat nil Γ (succ (succ (succ zero))) T_nat) nil)::nil))
      ::(N (TJ J_Nat nil Γ (succ (succ (succ (succ zero)))) T_nat) nil)::nil))::nil))
  ::(N (TJ J_App nil ((215,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) ttrue))::Γ) (app (app (fvar 6 term_var) (succ zero)) ((succ zero))) T_nat)
    ((N (TJ J_App nil ((215,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) ttrue))::Γ) (app (fvar 6 term_var) (succ zero)) (T_arrow T_nat T_nat))
      ((N (TJ J_Var nil ((215,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) ttrue))::Γ) (fvar 6 term_var) (T_arrow T_nat (T_arrow T_nat T_nat))) nil)
      ::(N (TJ J_Nat nil ((215,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) ttrue))::Γ) (succ zero) T_nat) nil)::nil))
    ::(N (TJ J_Nat nil ((215,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) ttrue))::Γ) (succ zero) T_nat) nil)::nil))
  ::(N (TJ J_App nil ((216,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) tfalse))::Γ) (app (app (fvar 6 term_var) (succ (succ zero))) ((succ (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))))) T_nat)
    ((N (TJ J_App nil ((216,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) tfalse))::Γ) (app (fvar 6 term_var) (succ (succ zero))) (T_arrow T_nat T_nat))
      ((N (TJ J_Var nil ((216,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) tfalse))::Γ) (fvar 6 term_var) (T_arrow T_nat (T_arrow T_nat T_nat))) nil)
      ::(N (TJ J_Nat nil ((216,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) tfalse))::Γ) (succ (succ zero)) T_nat) nil)::nil))
    ::(N (TJ J_Nat nil ((216,(T_equiv (app (app (fvar 5 term_var) (succ (succ (succ zero)))) ((succ (succ (succ (succ zero)))))) tfalse))::Γ) (succ (succ (succ (succ (succ (succ (succ (succ (succ zero))))))))) T_nat) nil)::nil))::nil))::nil).
 
Lemma derivationValid: List.forallb is_valid ds = true.
Proof. unfold ds, List.forallb, is_valid. reflexivity. Qed.
