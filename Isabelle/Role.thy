theory Role
  imports Main
begin

(* Role entity representation *)
record role = 
  role_id :: nat
  role_name :: string
  role_description :: string
  role_permissions :: "string list"

(* Role constructor with validation *)
fun make_role :: "nat ⇒ string ⇒ string ⇒ string list ⇒ role option" where
  "make_role rid name description permissions = 
    (if name ≠ [] then 
      Some [role_id = rid, role_name = name, role_description = description, 
            role_permissions = permissions]
     else None)"

(* Role operations *)
fun set_role_name :: "role ⇒ string ⇒ role option" where
  "set_role_name r name = 
    (if name ≠ [] then 
      Some (r⌊role_name := name⌋) 
     else None)"

fun set_role_description :: "role ⇒ string ⇒ role" where
  "set_role_description r description = r⌊role_description := description⌋"

fun add_permission :: "role ⇒ string ⇒ role" where
  "add_permission r permission = 
    (if permission ∈ set (role_permissions r) then r
     else r⌊role_permissions := (role_permissions r) @ [permission]⌋)"

fun remove_permission :: "role ⇒ string ⇒ role" where
  "remove_permission r permission = 
    r⌊role_permissions := filter (λp. p ≠ permission) (role_permissions r)⌋"

fun has_permission :: "role ⇒ string ⇒ bool" where
  "has_permission r permission = (permission ∈ set (role_permissions r))"

(* Role to array conversion *)
fun role_to_list :: "role ⇒ (string × string) list" where
  "role_to_list r = [
    (''id'', show (role_id r)),
    (''name'', role_name r),
    (''description'', role_description r),
    (''permissions'', concat (intersperse '','' (role_permissions r)))
  ]"

(* Properties and lemmas *)
lemma role_name_not_empty:
  "make_role rid name description permissions = Some r ⟹ name ≠ []"
  by (cases "name ≠ []") auto

lemma add_permission_idempotent:
  "has_permission r permission \<Longrightarrow> add_permission r permission = r"
  by (simp add: has_permission.simps add_permission.simps)

lemma remove_permission_effect:
  "\<not>has_permission (remove_permission r permission) permission"
  by (simp add: has_permission.simps remove_permission.simps)

lemma permission_preservation:
  "p \<noteq> permission \<Longrightarrow> 
   has_permission r p = has_permission (remove_permission r permission) p"
  by (simp add: has_permission.simps remove_permission.simps)

lemma add_permission_increases_or_same:
  "set (role_permissions r) \<subseteq> set (role_permissions (add_permission r permission))"
  by (cases "permission \<in> set (role_permissions r)") auto

end 