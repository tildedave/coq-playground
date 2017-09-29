Section definitions.

Require Import String List BinInt ZArith.
Import ListNotations.

Inductive func : Set := Plus | Sub | Mult : Z -> func.
Inductive relation  : Set := Eq | Lt | Cong : Z -> relation.

(* term: x + 1 = y ---> = + x 1 y  *)
(* http://lara.epfl.ch/w/_media/sav12:qe_presburger_arithmetic.pdf *)

Inductive atom : Set :=
| Atom_Var : string -> atom
| Atom_Const : Z -> atom.

Inductive term : Set :=
| Term_Atom : atom -> term
| Term_Func : func -> term -> term -> term.

Inductive literal : Type :=
| Literal_Relation : relation -> term -> term -> literal
| Literal_NotRelation : relation -> term -> term -> literal.

Inductive exp : Set :=
| Exp_Literal : literal -> exp
| Exp_Exists : (string -> exp) -> exp
| Exp_And : exp -> exp -> exp
| Exp_Or : exp -> exp -> exp
| Exp_Not : exp -> exp -> exp.

Inductive normalLiteral : Set :=
(* 0 < K_0 + K_i * x_i *)
| NormalLiteral_Gtz : Z -> list Z -> list string -> normalLiteral
| NormalLiteral_Congz : Z -> list Z -> list string -> normalLiteral.

Inductive conjunction : Type :=
| Conj_NormalLiteral : normalLiteral -> conjunction
| Conj_And : conjunction -> conjunction -> conjunction.

Inductive disjunction : Set :=
  | Disj_Conj : conjunction -> disjunction
  | Disj_Disj : conjunction -> disjunction -> disjunction.


(* (A v B) ^ (C v D) => (A v B) C v (A v B)D => AC v BC v AD v BD *)

Fixpoint conj_and_disjunction (c : conjunction) (d : disjunction) :=
    match d with
    | (Disj_Conj c') => Disj_Conj (Conj_And c c')
    | (Disj_Disj c' d') =>
        (* C ^ (C' + D) => C^C' + CD *)
        let c_and_c' := (Conj_And c c') in
        Disj_Disj c_and_c' (conj_and_disjunction c d')
    end.

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

Fixpoint disjunction_list_and (d1 d2 : list disjunction) : list disjunction :=
    match (d1, d2) with
    | ([], _) => d2
    | (_, []) => d1
    (* (X + D1')(Y + D2') = XY + XD2' + YD1' + D1'D2' *)
    | (x :: d1', y :: d2') =>
        (disjunction_and x y) :: (disjunction_and_helper x d2') ++ (disjunction_and_helper y d1') ++ (disjunction_list_and d1' d2')
    end.

Fixpoint collectTerms (r : relation) (t : term) : normalLiteral :=
    NormalLiteral_Congz Z0 [Zpos 1] [ (String "X" "") ].

Definition normalLiteralToDisjunction (nl : normalLiteral) :=
    (Disj_Conj (Conj_NormalLiteral nl)).

Definition isZeroTerm t : bool :=
    match t with
    | (Term_Atom (Atom_Const 0)) => true
    | _ => false
    end.

Fixpoint normalizeLiteral (l : literal) : disjunction :=
    match l with
    | (Literal_Relation r t1 t2) =>
        match r with
        | Eq =>
            let d1 := normalizeLiteral (Literal_Relation Lt t1 (Term_Func Plus t2 (Term_Atom (Atom_Const 1)))) in
            let d2 := normalizeLiteral (Literal_Relation Lt t2 (Term_Func Plus t1 (Term_Atom (Atom_Const 1)))) in
                disjunction_and d1 d2
        | Lt =>
            if isZeroTerm t1 then
                (normalLiteralToDisjunction (collectTerms Lt t2))
            else
                normalizeLiteral (Literal_Relation Lt (Term_Atom (Atom_Const 0)) (Term_Func Sub t2 t1))
        | (Cong k) =>
            if isZeroTerm t1 then
                (normalLiteralToDisjunction (collectTerms (Cong 0) t2))
            else
                normalizeLiteral (Literal_Relation (Cong k) (Term_Atom (Atom_Const 0)) (Term_Func Sub t2 t1))
        end
    | (Literal_NotRelation r t1 t2) =>
        match r with
        | Eq =>
            let d1 := normalizeLiteral (Literal_Relation Lt t1 t2) in
            let d2 := normalizeLiteral (Literal_Relation Lt t2 t1) in
                disjunction_or d1 d2
        | Lt =>
            normalizeLiteral (Literal_Relation Lt t2 (Term_Func Plus t1 (Term_Atom (Atom_Const 1))))
        | (Cong k) =>
            if isZeroTerm t1 then
                (congToDisjunction k (Zabs_nat k) t2)
            else
                normalizeLiteral (Literal_NotRelation (Cong k) (Term_Atom (Atom_Const 0)) (Term_Func Sub t2 t1))
        end
    end

    with congToDisjunction k n t :=
        match n with
        | O => Disj_Conj (Conj_NormalLiteral (NormalLiteral_Congz Z0 [] []))
        | (S m) => Disj_Disj
            (Conj_NormalLiteral (collectTerms (Cong 0) (Term_Func Plus t (Term_Atom (Atom_Const (Z_of_nat' m))))))
            (congToDisjunction k m t)
        end.

(* Combines two terms that are already DNF together *)
Fixpoint dnfOr (e1 e2 : expDnf) : expDnf :=
    match (e1, e2) with
    | (expDnf_Exists d1, expDnf_Exists d2) =>
        expDnf_Exists
            (fun (m : string) => expDnf_Exists
                (fun (n : string) => (dnfOr (d1 n) (d2 m))))
    | (expDnf_Exists d1, expDnf_Disjunction dl2) =>
        (expDnf_Exists
            (fun (m : string) => (dnfOr_helper (d1 m) dl2)))
    | (expDnf_Disjunction dl1, expDnf_Exists d2) =>
        (expDnf_Exists
            (fun (n : string) => (dnfOr_helper (d2 n) dl1)))
    | (expDnf_Disjunction dl1, expDnf_Disjunction dl2) =>
        (expDnf_Disjunction (rev_append dl1 dl2))
    end.

Eval simpl in (conj_and_disjunction (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "A"))) (Disj_Disj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "B"))) (Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "C")))))).

Fixpoint dnfAnd_helper (e1 : expDnf) (dl : list disjunction) : expDnf :=
    match e1 with
    | (expDnf_Exists d) =>
        expDnf_Exists (fun (m : string) => dnfAnd_helper (d m) dl)
    | (expDnf_Disjunction dl1) => expDnf_Disjunction (disjunction_list_and dl1 dl)
    end.

Fixpoint dnfAnd (e1 e2 : expDnf) : expDnf :=
    (* this is where terms can explode *)
    match (e1, e2) with
    | (expDnf_Exists d1, expDnf_Exists d2) =>
        expDnf_Exists
            (fun (m : string) => expDnf_Exists
                (fun (n : string) => (dnfAnd (d1 n) (d2 m))))
    | (expDnf_Exists d1, expDnf_Disjunction dl2) =>
        expDnf_Exists
            (fun (m : string) => (dnfAnd_helper (d1 m) dl2))
    | (expDnf_Disjunction dl1, expDnf_Exists d2) =>
        expDnf_Exists
            (fun (n : string) => (dnfAnd_helper (d2 n) dl1))
    | (expDnf_Disjunction dl1, expDnf_Disjunction dl2) =>
        (expDnf_Disjunction (disjunction_list_and dl1 dl2))
    end.

Fixpoint dnfConvert (e : exp) : expDnf :=
    match e with
    | (Exp_Term l) => (expDnf_Disjunction [Disj_Conj (Conj_Lit l)])
    | (Exp_Exists d) =>
        expDnf_Exists
            (fun (m : string) => dnfConvert (d m))
    | (Exp_And e1 e2) => dnfAnd (dnfConvert e1) (dnfConvert e2)
    | (Exp_Or e1 e2) => dnfOr (dnfConvert e1) (dnfConvert e2)
    end.

(* TODO: valuations, prove normalization is right *)


Eval simpl in (dnfConvert (Exp_Or (Exp_Term (Lit_Var "A")) (Exp_Term (Lit_Var "B")))).
Eval simpl in (dnfConvert (Exp_Or (Exp_Term (Lit_Var "C")) (Exp_Term (Lit_Var "D")))).

Eval simpl in dnfAnd
    (expDnf_Disjunction [Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "A"))); Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "B")))])
    (expDnf_Disjunction [Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "C"))); Disj_Conj (Conj_NormalLiteral (Ltz_LinearEquation 0 (Term_Atom (Atom_Var "D")))]).

Eval simpl in (dnfConvert (Exp_And
    (Exp_Or (Exp_Lit (Lit_Var "A")) (Exp_Lit (Lit_Var "B")))
    (Exp_Or (Exp_Lit (Lit_Var "C")) (Exp_Lit (Lit_Var "D"))))).


Eval simpl in (dnfConvert (Exp_And
    (Exp_Or (Exp_Lit (Lit_Var "A")) (Exp_Exists (fun a => (Exp_Lit (Lit_Var a)))))
    (Exp_Or (Exp_Lit (Lit_Var "C")) (Exp_Lit (Lit_Var "D"))))).

(*
    Ex Ey Ez (x  + y + z = 2)
    Ew Ex Ey Ez (x + y = w) ^ (w + z = 2)

*)

