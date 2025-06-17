theory UserApplication
  imports UserService
begin

(* Application state *)
record application_state = 
  user_service :: user_service_state
  output_log :: "string list"

(* Logging function *)
fun add_log :: "application_state ⇒ string ⇒ application_state" where
  "add_log state msg = state⌊output_log := (output_log state) @ [msg]⌋"

(* Display functions *)
fun display_user :: "user ⇒ string" where
  "display_user u = 
    ''ID: '' @ show (user_id u) @ 
    '', Name: '' @ user_name u @ 
    '', Email: '' @ user_email u @ 
    '', Status: '' @ (if user_is_active u then ''Active'' else ''Inactive'')"

fun display_users :: "user list ⇒ string list" where
  "display_users users = map display_user users"

(* Application operations *)
fun app_display_all_users :: "application_state ⇒ application_state" where
  "app_display_all_users state = 
    let users = service_get_all_users (user_service state);
        count = service_get_users_count (user_service state);
        logs = [''--- All Users ---''] @ display_users users @ [''Total users: '' @ show count] in
    state⌊output_log := (output_log state) @ logs⌋"

fun app_display_active_users :: "application_state ⇒ application_state" where
  "app_display_active_users state = 
    let users = service_get_active_users (user_service state);
        count = service_get_active_users_count (user_service state);
        logs = [''--- Active Users ---''] @ display_users users @ [''Active users: '' @ show count] in
    state⌊output_log := (output_log state) @ logs⌋"

fun app_create_user :: "application_state ⇒ string ⇒ string ⇒ application_state" where
  "app_create_user state email name = 
    (case service_create_user (user_service state) email name of
      (new_service, Success user) ⇒ 
        let log_msg = ''Created user: '' @ user_name user @ '' ('' @ user_email user @ '')'';
            new_state = state⌊user_service := new_service⌋ in
        add_log new_state log_msg
    | (new_service, Failure exc) ⇒ 
        let log_msg = ''Error: '' @ exception_message exc;
            new_state = state⌊user_service := new_service⌋ in
        add_log new_state log_msg)"

fun app_update_user :: "application_state ⇒ nat ⇒ string option ⇒ string option ⇒ application_state" where
  "app_update_user state id new_email new_name = 
    (case service_update_user (user_service state) id new_email new_name of
      (new_service, Success user) ⇒ 
        let log_msg = ''Updated user: '' @ user_name user;
            new_state = state⌊user_service := new_service⌋ in
        add_log new_state log_msg
    | (new_service, Failure exc) ⇒ 
        let log_msg = ''Error: '' @ exception_message exc;
            new_state = state⌊user_service := new_service⌋ in
        add_log new_state log_msg)"

fun app_deactivate_user :: "application_state ⇒ nat ⇒ application_state" where
  "app_deactivate_user state id = 
    (case service_deactivate_user (user_service state) id of
      (new_service, Success user) ⇒ 
        let log_msg = ''Deactivated user: '' @ user_name user;
            new_state = state⌊user_service := new_service⌋ in
        add_log new_state log_msg
    | (new_service, Failure exc) ⇒ 
        let log_msg = ''Error: '' @ exception_message exc;
            new_state = state⌊user_service := new_service⌋ in
        add_log new_state log_msg)"

fun app_find_user :: "application_state ⇒ nat ⇒ application_state" where
  "app_find_user state id = 
    (case service_get_user_by_id (user_service state) id of
      Success user ⇒ 
        let log_msg = ''Found user: '' @ display_user user in
        add_log state log_msg
    | Failure exc ⇒ 
        let log_msg = ''Error: '' @ exception_message exc in
        add_log state log_msg)"

(* Main application workflow *)
fun run_application :: "application_state" where
  "run_application = 
    let initial_state = ⌊user_service = init_user_service, output_log = [''=== User Management Application ==='']⌋;
        state1 = app_display_all_users initial_state;
        state2 = add_log state1 ''--- Creating new user ---'';
        state3 = app_create_user state2 ''newuser@example.com'' ''New User'';
        state4 = app_display_all_users state3;
        state5 = add_log state4 ''--- Updating user ---'';
        state6 = app_update_user state5 4 None (Some ''Updated User Name'');
        state7 = add_log state6 ''--- Deactivating user ---'';
        state8 = app_deactivate_user state7 4;
        state9 = app_display_active_users state8;
        state10 = add_log state9 ''--- Trying to find non-existent user ---'';
        state11 = app_find_user state10 999;
        final_state = add_log state11 ''=== Application finished ==='' in
    final_state"

(* Application properties *)
lemma application_logging_monotonic:
  "length (output_log (add_log state msg)) = length (output_log state) + 1"
  by simp

lemma application_preserves_service_invariants:
  "app_create_user state email name = new_state ⟹
   (∃user. service_get_user_by_email (user_service new_state) email = Success user) ∨
   (∃exc. service_get_user_by_email (user_service new_state) email = Failure exc)"
  by (cases "service_create_user (user_service state) email name") 
     (auto simp: app_create_user.simps split: user_result.splits)

lemma application_state_consistency:
  "app_display_all_users state = new_state ⟹
   service_get_all_users (user_service state) = service_get_all_users (user_service new_state)"
  by (simp add: app_display_all_users.simps)

(* Example execution *)
definition example_run :: "string list" where
  "example_run = output_log run_application"

(* Correctness properties *)
lemma run_application_creates_user:
  "∃user. service_get_user_by_email (user_service run_application) ''newuser@example.com'' = Success user"
  by (simp add: run_application.simps app_create_user.simps service_create_user.simps
               init_user_service.simps init_user_store.simps repo_find_by_email.simps
               make_user.simps is_valid_email.simps repo_save.simps Let_def)

lemma run_application_logs_operations:
  "length (output_log run_application) > 10"
  by (simp add: run_application.simps app_display_all_users.simps app_create_user.simps
               app_update_user.simps app_deactivate_user.simps app_display_active_users.simps
               app_find_user.simps add_log.simps)

end 