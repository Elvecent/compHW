Require Import Coq.Lists.List.
Import ListNotations.

Open Scope list_scope.

Inductive ExpSort :=
| Literal : ExpSort
| NonLiteral : ExpSort.

Inductive ExpForm :=
| Single : ExpSort -> ExpForm
| Double : ExpSort -> ExpSort -> ExpForm.

Definition fuse_forms ef1 ef2 : ExpForm :=
  match ef1, ef2 with
  | Single _, Single _ => Double Literal Literal
  | Single _, Double _ _ => Double Literal NonLiteral
  | Double _ _, Single _ => Double NonLiteral Literal
  | Double _ _, Double _ _ => Double NonLiteral NonLiteral
  end.

Inductive Exp : ExpForm -> Type :=
| ExpLit : nat -> Exp (Single Literal)
| ExpOp : forall {X Y}, (nat -> nat -> nat) -> Exp X -> Exp Y -> Exp (fuse_forms X Y).

Coercion nat_exp := fun n : nat => ExpLit n.
Infix "+" := (fun a b => ExpOp plus a b) : exp_scope.
Infix "*" := (fun a b => ExpOp mult a b) : exp_scope.

Open Scope exp_scope.

Check ((1 + 2) * 3).

Lemma fuse_yields_double : forall x y z, fuse_forms x y <> Single z.
Proof.
  intros. destruct x, y;
            intros H; inversion H.
Qed.

Definition eval_lit : forall (e : Exp (Double Literal Literal)),
    Exp (Single Literal).
Proof.
  intros. inversion e.
  inversion H1; subst.
  inversion H2; subst.
  - apply ExpLit. exact (H0 H3 H4).
  - destruct (fuse_forms X Y0) eqn:HH.
    + apply fuse_yields_double in HH.
      congruence.
    + simpl in H. inversion H.
  - destruct (fuse_forms X0 Y0) eqn:HH.
    + apply fuse_yields_double in HH.
      inversion HH.
    + simpl in H. destruct Y; inversion H.
Defined.

Inductive EvalTree : forall {ef1 ef2 : ExpForm}, Exp ef1 -> Exp ef2 -> Type :=
| ReflEval : forall {ef} (e : Exp ef), EvalTree e e
| OpEval : forall (e : Exp (Double Literal Literal)),
    EvalTree e (eval_lit e)
| LeftEval : forall op {h1 h2} {ef1 ef2}
               (e : Exp (Double h1 h2))
               (e' : Exp ef1)
               (ee : Exp ef2),
    EvalTree e e' -> EvalTree (ExpOp op e ee) (ExpOp op e' ee)
| RightEval : forall op {h1 h2} {ef1}
                (e : Exp (Double h1 h2))
                (e' : Exp ef1)
                (ee : Exp (Single Literal)),
    EvalTree e e' -> EvalTree (ExpOp op ee e) (ExpOp op ee e').

Fixpoint eval {ef1} (e : Exp ef1) :
  sigT (fun ef2 => sigT (fun (e' : Exp ef2) => EvalTree e e')).
Proof.
  intros. destruct e eqn:He.
  - rewrite <- He. exists (Single Literal), e. apply ReflEval.
  - inversion e0_1; inversion e0_2.
    + subst X Y. rewrite <- He.
      exists (Single Literal), (eval_lit e). apply OpEval.
    + subst X. remember (eval Y e0_2) as r.
      clear Heqr.
      destruct r, s.
      destruct Y.
      apply fuse_yields_double in H4.
      inversion H4.
      apply (RightEval n e0_2 _ e0_1) in e0.
      repeat eexists.
      eassumption.
    + subst Y. remember (eval X e0_1) as r.
      clear Heqr. destruct r, s.
      destruct X. apply fuse_yields_double in H2.
      inversion H2.
      apply (LeftEval n e0_1 _ e0_2) in e0.
      repeat eexists.
      eassumption.
    + subst Y. remember (eval X e0_1) as r.
      clear Heqr. destruct r, s.
      destruct X. apply fuse_yields_double in H2.
      inversion H2.
      apply (LeftEval n e0_1 _ e0_2) in e0.
      repeat eexists.
      eassumption.
Defined.

Definition extract_tree_type
           {ef1} {e : Exp ef1}
           (t : sigT (fun ef2 => sigT (fun (e' : Exp ef2) => EvalTree e e'))) :
  Type.
Proof.
  destruct t.
  destruct s.
  exact (EvalTree e x0).
Defined.
  
Definition extract_tree
           {ef1} {e : Exp ef1}
           (t : sigT (fun ef2 => sigT (fun (e' : Exp ef2) => EvalTree e e'))) :
  (extract_tree_type t).
Proof.
  unfold extract_tree_type.
  destruct t. destruct s.
  assumption.
Defined.

Inductive Rule :=
| Delta : Rule
| Left : Rule
| Right : Rule.

Fixpoint print_eval_tree
         {ef1 ef2}
         {e1 : Exp ef1}
         {e2 : Exp ef2}
         (t : EvalTree e1 e2) : list Rule :=
  match t with
  | ReflEval _ => []
  | OpEval _ => [Delta]
  | LeftEval _ _ _ _ t' => Left :: print_eval_tree t'
  | RightEval _ _ _ _ t' => Right :: print_eval_tree t'
  end.

Example ev_tree := extract_tree (eval (1 + 2)).

Compute ev_tree.
Compute (print_eval_tree ev_tree).

Example ev_tree0 := extract_tree (eval (1 + (2 * 3))).

Compute ev_tree0.
Compute (print_eval_tree ev_tree0).

Example ev_tree1 := extract_tree (eval ((1 + 2) * 3)).

Compute ev_tree1.
Compute (print_eval_tree ev_tree1).