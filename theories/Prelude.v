(** * Prelude: composition, endomorphisms, monoids *)

From Stdlib Require Export FunctionalExtensionality.

(** Function composition [f ∘ g]: the left operand acts after the right. *)
Definition comp {A B C : Type} (f : B -> C) (g : A -> B) : A -> C :=
  fun x => f (g x).
Arguments comp {A B C} f g x /.
Notation "f ∘ g" := (comp f g) (at level 40, left associativity).

(** Identity function (shadows the stdlib's [id], whose type argument is
    explicit). *)
Definition id {A : Type} (x : A) : A := x.

(** [End Γ]: the transformations [Γ → Γ]. *)
Definition End (A : Type) : Type := A -> A.

(** A monoid structure [(op, u)] on a carrier [M]. *)
Record IsMonoid {M : Type} (op : M -> M -> M) (u : M) : Prop := {
  m_assoc : forall a b c, op a (op b c) = op (op a b) c;
  m_id_l : forall a, op u a = a;
  m_id_r : forall a, op a u = a
}.

(** A monoid homomorphism. *)
Record IsMonoidHom {M N : Type}
    (opM : M -> M -> M) (uM : M) (opN : N -> N -> N) (uN : N)
    (h : M -> N) : Prop := {
  hom_unit : h uM = uN;
  hom_mul : forall a b, h (opM a b) = opN (h a) (h b)
}.

(** A subset closed under the unit and the operation. *)
Definition IsSubmonoid {M : Type} (op : M -> M -> M) (u : M) (P : M -> Prop)
  : Prop :=
  P u /\ forall a b, P a -> P b -> P (op a b).

(** [End Γ] is a monoid under composition. *)
Lemma End_monoid (A : Type) : IsMonoid (@comp A A A) id.
Proof. split; reflexivity. Qed.
