theory Coffee
  imports Main
begin

(* Типы зерен *)
datatype beans = Arabica | Robusta

(* Типы молока *)
datatype milk = WholeMilk | AlmondMilk

(* Функция получения цены зерен *)
fun beans_price :: "beans ⇒ real" where
  "beans_price Arabica = 45" |
  "beans_price Robusta = 30"

(* Функция получения времени варки зерен *)
fun brewing_time :: "beans ⇒ nat" where
  "brewing_time Arabica = 120" |
  "brewing_time Robusta = 90"

(* Функция получения цены молока *)
fun milk_price :: "milk ⇒ real" where
  "milk_price WholeMilk = 15" |
  "milk_price AlmondMilk = 25"

(* Константы *)
definition max_price :: real where "max_price = 100"
definition base_barista_fee :: real where "base_barista_fee = 5"

(* Функция расчета надбавки бариста *)
fun barista_fee_percent :: "beans ⇒ real" where
  "barista_fee_percent b = base_barista_fee + (real (brewing_time b) / 1000)"

(* Функция расчета итоговой цены кофе *)
fun coffee_price :: "beans ⇒ milk ⇒ real" where
  "coffee_price b m = 
    let base_price = beans_price b + milk_price m;
        fee_percent = barista_fee_percent b;
        barista_fee = base_price * (fee_percent / 100)
    in base_price + barista_fee"

(* Вспомогательные леммы для структурного анализа *)

(* Максимальная цена зерен *)
fun max_beans_price :: real where
  "max_beans_price = Max {beans_price b | b. True}"

(* Максимальная цена молока *)  
fun max_milk_price :: real where
  "max_milk_price = Max {milk_price m | m. True}"

(* Максимальное время варки *)
fun max_brewing_time :: nat where
  "max_brewing_time = Max {brewing_time b | b. True}"

(* Конкретные значения максимумов *)
lemma max_beans_price_value: "max_beans_price = max (beans_price Arabica) (beans_price Robusta)"
  by (simp add: max_beans_price.simps)

lemma max_milk_price_value: "max_milk_price = max (milk_price WholeMilk) (milk_price AlmondMilk)"
  by (simp add: max_milk_price.simps)

lemma max_brewing_time_value: "max_brewing_time = max (brewing_time Arabica) (brewing_time Robusta)"
  by (simp add: max_brewing_time.simps)

(* Верхняя граница для надбавки бариста *)
lemma barista_fee_percent_bounded:
  "∀b. barista_fee_percent b ≤ base_barista_fee + (real max_brewing_time / 1000)"
proof
  fix b
  show "barista_fee_percent b ≤ base_barista_fee + (real max_brewing_time / 1000)"
  proof (cases b)
    case Arabica
    then show ?thesis 
      by (simp add: barista_fee_percent.simps brewing_time.simps 
                   max_brewing_time_value base_barista_fee_def)
  next
    case Robusta  
    then show ?thesis
      by (simp add: barista_fee_percent.simps brewing_time.simps 
                   max_brewing_time_value base_barista_fee_def)
  qed
qed

(* Верхняя граница для базовой цены *)
lemma base_price_bounded:
  "∀b m. beans_price b + milk_price m ≤ max_beans_price + max_milk_price"
proof (intro allI)
  fix b m
  show "beans_price b + milk_price m ≤ max_beans_price + max_milk_price"
  proof (cases b)
    case Arabica
    then show ?thesis
    proof (cases m)
      case WholeMilk
      with Arabica show ?thesis 
        by (simp add: beans_price.simps milk_price.simps 
                     max_beans_price_value max_milk_price_value)
    next
      case AlmondMilk
      with Arabica show ?thesis
        by (simp add: beans_price.simps milk_price.simps 
                     max_beans_price_value max_milk_price_value)
    qed
  next
    case Robusta
    then show ?thesis
    proof (cases m)
      case WholeMilk
      with Robusta show ?thesis
        by (simp add: beans_price.simps milk_price.simps 
                     max_beans_price_value max_milk_price_value)
    next
      case AlmondMilk
      with Robusta show ?thesis
        by (simp add: beans_price.simps milk_price.simps 
                     max_beans_price_value max_milk_price_value)
    qed
  qed
qed

(* Основная теорема: структурное доказательство *)
theorem coffee_price_bounded:
  "∀b m. coffee_price b m ≤ max_price"
proof (intro allI)
  fix b m
  
  (* Разложим формулу цены *)
  have price_formula: "coffee_price b m = 
    let base_price = beans_price b + milk_price m;
        fee_percent = barista_fee_percent b;
        barista_fee = base_price * (fee_percent / 100)
    in base_price + barista_fee"
    by (simp add: coffee_price.simps)
  
  (* Упростим *)
  have simplified: "coffee_price b m = 
    (beans_price b + milk_price m) * (1 + barista_fee_percent b / 100)"
    by (simp add: coffee_price.simps Let_def algebra_simps)
  
  (* Используем верхние границы *)
  have "coffee_price b m ≤ 
    (max_beans_price + max_milk_price) * (1 + (base_barista_fee + real max_brewing_time / 1000) / 100)"
  proof -
    have base_bound: "beans_price b + milk_price m ≤ max_beans_price + max_milk_price"
      using base_price_bounded by blast
    have fee_bound: "barista_fee_percent b ≤ base_barista_fee + real max_brewing_time / 1000"
      using barista_fee_percent_bounded by blast
    
    from base_bound fee_bound show ?thesis
      by (simp add: simplified mult_mono add_mono divide_right_mono)
  qed
  
     (* Вычисляем абстрактную верхнюю границу через максимумы *)
   also have "... = (max_beans_price + max_milk_price) * 
                    (1 + (base_barista_fee + real max_brewing_time / 1000) / 100)"
     by (simp add: max_beans_price_value max_milk_price_value max_brewing_time_value 
                  beans_price.simps milk_price.simps brewing_time.simps base_barista_fee_def)
   
   finally have upper_bound: "coffee_price b m ≤ 
     (max_beans_price + max_milk_price) * (1 + (base_barista_fee + real max_brewing_time / 1000) / 100)" .
   
   (* Показываем, что верхняя граница меньше максимума *)
   have bound_safe: "(max_beans_price + max_milk_price) * 
                     (1 + (base_barista_fee + real max_brewing_time / 1000) / 100) ≤ max_price"
   proof -
     (* Используем конкретные значения только для финальной проверки *)
     have concrete_bound: "(max_beans_price + max_milk_price) * 
                          (1 + (base_barista_fee + real max_brewing_time / 1000) / 100) = 
                          (max (beans_price Arabica) (beans_price Robusta) + 
                           max (milk_price WholeMilk) (milk_price AlmondMilk)) *
                          (1 + (base_barista_fee + real (max (brewing_time Arabica) (brewing_time Robusta)) / 1000) / 100)"
       by (simp add: max_beans_price_value max_milk_price_value max_brewing_time_value)
     
     (* Подставляем только для финальной проверки *)
     also have "... = (max 45 30 + max 15 25) * (1 + (5 + real (max 120 90) / 1000) / 100)"
       by (simp add: beans_price.simps milk_price.simps brewing_time.simps base_barista_fee_def)
     
     also have "... = 73.584"
       by simp
     
     finally have "73.584 ≤ max_price" by (simp add: max_price_def)
     
     with concrete_bound show ?thesis by simp
   qed
   
   with upper_bound show "coffee_price b m ≤ max_price"
     by linarith
qed

(* Дополнительные структурные леммы *)

(* Максимальная цена достигается на самых дорогих ингредиентах *)
lemma max_price_combination:
  "∀b m. coffee_price b m ≤ coffee_price Arabica AlmondMilk"
proof (intro allI)
  fix b m
  have "coffee_price b m = (beans_price b + milk_price m) * (1 + barista_fee_percent b / 100)"
    by (simp add: coffee_price.simps Let_def algebra_simps)
  also have "... ≤ (beans_price Arabica + milk_price AlmondMilk) * (1 + barista_fee_percent Arabica / 100)"
  proof -
    have beans_max: "beans_price b ≤ beans_price Arabica"
      by (cases b) (simp_all add: beans_price.simps)
    have milk_max: "milk_price m ≤ milk_price AlmondMilk"  
      by (cases m) (simp_all add: milk_price.simps)
    have fee_max: "barista_fee_percent b ≤ barista_fee_percent Arabica"
      by (cases b) (simp_all add: barista_fee_percent.simps brewing_time.simps)
    
    from beans_max milk_max fee_max show ?thesis
      by (simp add: mult_mono add_mono divide_right_mono)
  qed
  also have "... = coffee_price Arabica AlmondMilk"
    by (simp add: coffee_price.simps Let_def algebra_simps)
  finally show "coffee_price b m ≤ coffee_price Arabica AlmondMilk" .
qed

(* Минимальная цена достигается на самых дешевых ингредиентах *)
lemma min_price_combination:
  "∀b m. coffee_price Robusta WholeMilk ≤ coffee_price b m"
proof (intro allI)
  fix b m
  have "coffee_price Robusta WholeMilk = (beans_price Robusta + milk_price WholeMilk) * (1 + barista_fee_percent Robusta / 100)"
    by (simp add: coffee_price.simps Let_def algebra_simps)
  also have "... ≤ (beans_price b + milk_price m) * (1 + barista_fee_percent b / 100)"
  proof -
    have beans_min: "beans_price Robusta ≤ beans_price b"
      by (cases b) (simp_all add: beans_price.simps)
    have milk_min: "milk_price WholeMilk ≤ milk_price m"
      by (cases m) (simp_all add: milk_price.simps)
    have fee_min: "barista_fee_percent Robusta ≤ barista_fee_percent b"
      by (cases b) (simp_all add: barista_fee_percent.simps brewing_time.simps)
    
    from beans_min milk_min fee_min show ?thesis
      by (simp add: mult_mono add_mono divide_right_mono)
  qed
  also have "... = coffee_price b m"
    by (simp add: coffee_price.simps Let_def algebra_simps)
  finally show "coffee_price Robusta WholeMilk ≤ coffee_price b m" .
qed

(* Структурное свойство: цена растет с ростом цен ингредиентов *)
lemma price_monotonic_in_beans:
  "beans_price b1 ≤ beans_price b2 ⟹ brewing_time b1 ≤ brewing_time b2 ⟹ 
   coffee_price b1 m ≤ coffee_price b2 m"
proof -
  assume beans_le: "beans_price b1 ≤ beans_price b2"
  assume time_le: "brewing_time b1 ≤ brewing_time b2"
  
  have fee_le: "barista_fee_percent b1 ≤ barista_fee_percent b2"
    using time_le by (simp add: barista_fee_percent.simps)
  
  have "coffee_price b1 m = (beans_price b1 + milk_price m) * (1 + barista_fee_percent b1 / 100)"
    by (simp add: coffee_price.simps Let_def algebra_simps)
  also have "... ≤ (beans_price b2 + milk_price m) * (1 + barista_fee_percent b2 / 100)"
    using beans_le fee_le by (simp add: mult_mono add_mono divide_right_mono)
  also have "... = coffee_price b2 m"
    by (simp add: coffee_price.simps Let_def algebra_simps)
  finally show "coffee_price b1 m ≤ coffee_price b2 m" .
qed

(* Значительный запас безопасности *)
lemma significant_safety_margin:
  "∀b m. coffee_price b m ≤ max_price - 25"
proof
  fix b m
  have "coffee_price b m ≤ coffee_price Arabica AlmondMilk"
    using max_price_combination by blast
  also have "coffee_price Arabica AlmondMilk = 
    (beans_price Arabica + milk_price AlmondMilk) * (1 + barista_fee_percent Arabica / 100)"
    by (simp add: coffee_price.simps Let_def algebra_simps)
  also have "... ≤ (max_beans_price + max_milk_price) * 
                   (1 + (base_barista_fee + real max_brewing_time / 1000) / 100)"
  proof -
    have "beans_price Arabica ≤ max_beans_price"
      by (simp add: max_beans_price_value beans_price.simps)
    have "milk_price AlmondMilk ≤ max_milk_price"  
      by (simp add: max_milk_price_value milk_price.simps)
    have "barista_fee_percent Arabica ≤ base_barista_fee + real max_brewing_time / 1000"
      using barista_fee_percent_bounded by blast
    thus ?thesis
      by (simp add: mult_mono add_mono divide_right_mono)
  qed
  also have "... ≤ max_price - 25"
  proof -
    (* Только здесь используем конкретное вычисление для проверки *)
    have bound_value: "(max_beans_price + max_milk_price) * 
                      (1 + (base_barista_fee + real max_brewing_time / 1000) / 100) = 73.584"
      by (simp add: max_beans_price_value max_milk_price_value max_brewing_time_value 
                   beans_price.simps milk_price.simps brewing_time.simps base_barista_fee_def)
    thus ?thesis by (simp add: max_price_def)
  qed
  finally show "coffee_price b m ≤ max_price - 25" .
qed

end 