theory UserRepository
  imports User UserExceptions
begin

(* User repository interface as locale *)
locale user_repository =
  fixes
    find_by_id :: "nat ⇒ user option" and
    find_by_email :: "string ⇒ user option" and
    find_all :: "unit ⇒ user list" and
    save :: "user ⇒ unit" and
    delete :: "nat ⇒ bool" and
    find_active :: "unit ⇒ user list"
  assumes
    (* Basic consistency constraints *)
    find_by_id_consistency: "find_by_id id = Some u ⟹ user_id u = id"
    and find_by_email_consistency: "find_by_email email = Some u ⟹ user_email u = email"
    and find_all_contains_by_id: "find_by_id id = Some u ⟹ u ∈ set (find_all ())"
    and find_active_are_active: "u ∈ set (find_active ()) ⟹ user_is_active u"
    and find_active_subset: "set (find_active ()) ⊆ set (find_all ())"

(* In-memory repository implementation *)
record user_store = 
  users :: "user list"
  next_id :: nat

(* Initialize repository with test data *)
definition init_user_store :: user_store where
  "init_user_store = (case 
    (make_user 1 ''admin@example.com'' ''Administrator'' True,
     make_user 2 ''user@example.com'' ''Regular User'' True,
     make_user 3 ''inactive@example.com'' ''Inactive User'' False) of
    (Some u1, Some u2, Some u3) ⇒ 
      ⌊users = [u1, u2, u3], next_id = 4⌋
    | _ ⇒ ⌊users = [], next_id = 1⌋)"

(* Repository operations *)
fun repo_find_by_id :: "user_store ⇒ nat ⇒ user option" where
  "repo_find_by_id store id = find (λu. user_id u = id) (users store)"

fun repo_find_by_email :: "user_store ⇒ string ⇒ user option" where
  "repo_find_by_email store email = find (λu. user_email u = email) (users store)"

fun repo_find_all :: "user_store ⇒ user list" where
  "repo_find_all store = users store"

fun repo_save :: "user_store ⇒ user ⇒ user_store" where
  "repo_save store u = 
    (if user_id u = 0 then
      (* Create new user with next available ID *)
      let new_user = u⌊user_id := next_id store⌋ in
      store⌊users := (users store) @ [new_user], next_id := (next_id store) + 1⌋
     else
      (* Update existing user *)
      let updated_users = map (λold_u. if user_id old_u = user_id u then u else old_u) (users store) in
      store⌊users := updated_users⌋)"

fun repo_delete :: "user_store ⇒ nat ⇒ user_store × bool" where
  "repo_delete store id = 
    (let new_users = filter (λu. user_id u ≠ id) (users store) in
     (store⌊users := new_users⌋, length (users store) ≠ length new_users))"

fun repo_find_active :: "user_store ⇒ user list" where
  "repo_find_active store = filter user_is_active (users store)"

(* Interpretation of the repository interface *)
interpretation in_memory_repo: user_repository 
  "repo_find_by_id init_user_store"
  "repo_find_by_email init_user_store" 
  "λ_. repo_find_all init_user_store"
  "λ_. ()"
  "λid. snd (repo_delete init_user_store id)"
  "λ_. repo_find_active init_user_store"
proof
  show "repo_find_by_id init_user_store id = Some u ⟹ user_id u = id" for id u
    by (simp add: repo_find_by_id.simps find_Some_iff)
  show "repo_find_by_email init_user_store email = Some u ⟹ user_email u = email" for email u
    by (simp add: repo_find_by_email.simps find_Some_iff)
  show "repo_find_by_id init_user_store id = Some u ⟹ u ∈ set (repo_find_all init_user_store)" for id u
    by (simp add: repo_find_by_id.simps repo_find_all.simps find_Some_iff)
  show "u ∈ set (repo_find_active init_user_store) ⟹ user_is_active u" for u
    by (simp add: repo_find_active.simps)
  show "set (repo_find_active init_user_store) ⊆ set (repo_find_all init_user_store)"
    by (simp add: repo_find_active.simps repo_find_all.simps)
qed

(* Repository properties *)
lemma save_preserves_existing_users:
  "u ∈ set (users store) ⟹ user_id u ≠ user_id new_u ⟹ 
   u ∈ set (users (repo_save store new_u))"
  by (cases "user_id new_u = 0") (auto simp: Let_def)

lemma delete_removes_user:
  "repo_find_by_id (fst (repo_delete store id)) id = None"
  by (simp add: repo_delete.simps repo_find_by_id.simps find_None_iff Let_def)

lemma find_active_correct:
  "u ∈ set (repo_find_active store) ⟷ u ∈ set (users store) ∧ user_is_active u"
  by (simp add: repo_find_active.simps)

end 