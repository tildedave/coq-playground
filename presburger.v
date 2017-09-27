Section definitions.

Require Import String List.
Import ListNotations.


Inductive binop : Set := Plus | Sub | Lt | Eq.

(* Literal: x + 1 = y ---> = + x 1 y  *)
(* Potentially also congruence *)

Inductive literal : Type :=
| Lit_Binop : binop -> literal -> literal -> literal
| Lit_Var : string -> literal
| Lit_Const : nat -> literal.

Inductive exp : Set :=
| Exp_Lit : literal -> exp
| Exp_Exists : string -> exp -> exp
| Exp_And : exp -> exp -> exp
| Exp_Or : exp -> exp -> exp.
(* TODO: support NOT *)

Inductive conjunction : Type :=
| Conj_Lit : literal -> conjunction
| Conj_NotLit : literal -> conjunction
| Conj_And : conjunction -> conjunction -> conjunction.

Inductive disjunction : Set :=
  | Disj_Conj : conjunction -> disjunction
  | Disj_Disj : conjunction -> disjunction -> disjunction.

Inductive expDnf : Type :=
  | expDnf_Exists : list string -> list disjunction -> expDnf
  | expDnf_Disjunction : list disjunction -> expDnf.

(* Combines two terms that are already DNF together *)
Fixpoint dnfOr (e1 e2 : expDnf) : expDnf :=
    match (e1, e2) with
    | (expDnf_Exists xl dl1, expDnf_Exists yl dl2) =>
        (* TODO: xl must not capture variables in e2 *)
        (expDnf_Exists (rev_append xl yl) (rev_append dl1 dl2))
    | (expDnf_Exists xl dl1, expDnf_Disjunction dl2) =>
        (expDnf_Exists xl (rev_append dl1 dl2))
    | (expDnf_Disjunction dl1, expDnf_Exists yl dl2) =>
        (expDnf_Exists yl (rev_append dl1 dl2))
    | (expDnf_Disjunction dl1, expDnf_Disjunction dl2) =>
        (expDnf_Disjunction (rev_append dl1 dl2))
    end.

(* (A v B) ^ (C v D) => (A v B) C v (A v B)D => AC v BC v AD v BD *)

Fixpoint conj_and_disjunction (c : conjunction) (d : disjunction) :=
    match d with
    | (Disj_Conj c') => Disj_Conj (Conj_And c c')
    | (Disj_Disj c' d') =>
        (* C ^ (C' + D) => C^C' + CD *)
        let c_and_c' := (Conj_And c c') in
        Disj_Disj c_and_c' (conj_and_disjunction c d')
    end.

Eval simpl in (conj_and_disjunction (Conj_Lit (Lit_Var "A")) (Disj_Disj (Conj_Lit (Lit_Var "B")) (Disj_Conj (Conj_Lit (Lit_Var "C"))))).

Fixpoint disjunction_or (d1 d2 : disjunction) : disjunction :=
  match d1 with
  | (Disj_Conj c') => (Disj_Disj c' d2)
  | (Disj_Disj c' d1') => (Disj_Disj c' (disjunction_or d1' d2))
  end.

Fixpoint disjunction_and (d1 d2 : disjunction) : disjunction :=
    match d1 with
    | (Disj_Conj c') => conj_and_disjunction c' d2
    (* (C v D1') * D2) = CD2 v D1'D2 *)
    | (Disj_Disj c' d1') =>
        let c'_and_d2 := (conj_and_disjunction c' d2) in
        (disjunction_or c'_and_d2 (disjunction_and d1' d2))
    end.


Fixpoint disjunction_and_helper (d : disjunction) (dl : list disjunction) {struct d} : list disjunction :=
    match d with
    | (Disj_Conj c') => map (fun x => conj_and_disjunction c' x) dl
    (* (C' + DL')(DL) = C'DL + DL'DL *)
    | (Disj_Disj c' d') => map (fun x => conj_and_disjunction c' x) dl ++ (disjunction_and_helper d' dl)
    end.


Eval simpl in disjunction_and_helper
    (Disj_Conj (Conj_Lit (Lit_Var "A"))) [Disj_Conj (Conj_Lit (Lit_Var "D"))].

Eval simpl in conj_and_disjunction (Conj_Lit (Lit_Var "A")) (Disj_Conj (Conj_Lit (Lit_Var "B"))).

Fixpoint disjunction_list_and (d1 d2 : list disjunction) : list disjunction :=
    match (d1, d2) with
    | ([], _) => d2
    | (_, []) => d1
    (* (X + D1')(Y + D2') = XY + XD2' + YD1' + D1'D2' *)
    | (x :: d1', y :: d2') =>
        (disjunction_and x y) :: (disjunction_and_helper x d2') ++ (disjunction_and_helper y d1') ++ (disjunction_list_and d1' d2')
    end.

Fixpoint dnfAnd (e1 e2 : expDnf) : expDnf :=
    (* this is where terms can explode *)
    match (e1, e2) with
    | (expDnf_Exists xl dl1, expDnf_Exists yl dl2) =>
        (* TODO: xl must not capture variables in e2 *)
        (expDnf_Exists (rev_append xl yl) (rev_append dl1 dl2))
    | (expDnf_Exists xl dl1, expDnf_Disjunction dl2) =>
        (expDnf_Exists xl (rev_append dl1 dl2))
    | (expDnf_Disjunction dl1, expDnf_Exists yl dl2) =>
        (expDnf_Exists yl (rev_append dl1 dl2))
    | (expDnf_Disjunction dl1, expDnf_Disjunction dl2) =>
        (expDnf_Disjunction (disjunction_list_and dl1 dl2))
    end.

Fixpoint dnfConvert (e : exp) : expDnf :=
    match e with
    | (Exp_Lit l) => (expDnf_Disjunction [Disj_Conj (Conj_Lit l)])
    (* TODO: will need to ensure this doesn't capture any variable *)
    | (Exp_Exists x e) =>
        let dnf_e := (dnfConvert e) in
        match dnf_e with
        | expDnf_Exists yl dl => (expDnf_Exists (cons x yl) dl)
        | expDnf_Disjunction dl => (expDnf_Exists (cons x nil) dl)
        end
    (* TODO: this is where we get term explosion *)
    | (Exp_And e1 e2) => dnfAnd (dnfConvert e1) (dnfConvert e2)
    | (Exp_Or e1 e2) => dnfOr (dnfConvert e1) (dnfConvert e2)
    end.

Eval simpl in (dnfConvert (Exp_Or (Exp_Lit (Lit_Var "A")) (Exp_Lit (Lit_Var "B")))).
Eval simpl in (dnfConvert (Exp_Or (Exp_Lit (Lit_Var "C")) (Exp_Lit (Lit_Var "D")))).

Eval simpl in dnfAnd
    (expDnf_Disjunction [Disj_Conj (Conj_Lit (Lit_Var "A")); Disj_Conj (Conj_Lit (Lit_Var "B"))])
    (expDnf_Disjunction [Disj_Conj (Conj_Lit (Lit_Var "C")); Disj_Conj (Conj_Lit (Lit_Var "D"))]).

Eval simpl in (dnfConvert (Exp_And
    (Exp_Or (Exp_Lit (Lit_Var "A")) (Exp_Lit (Lit_Var "B")))
    (Exp_Or (Exp_Lit (Lit_Var "C")) (Exp_Lit (Lit_Var "D"))))).
