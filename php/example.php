<?php

require_once 'vendor/autoload.php';

use Coffee\Beans\ArabicaBeans;
use Coffee\Beans\RobustaBeans;
use Coffee\Milk\WholeMilk;
use Coffee\Milk\AlmondMilk;
use Coffee\Service\CoffeeService;

$coffeeService = new CoffeeService();

// Все возможные комбинации
$beanTypes = [new ArabicaBeans(), new RobustaBeans()];
$milkTypes = [new WholeMilk(), new AlmondMilk()];

echo "=== Coffee Brewing System ===\n\n";

foreach ($beanTypes as $beans) {
    foreach ($milkTypes as $milk) {
        try {
            $result = $coffeeService->brewCoffee($beans, $milk);
            
            echo "Coffee: {$result['beans']} + {$result['milk']}\n";
            echo "Beans price: {$result['beans_price']}\n";
            echo "Milk price: {$result['milk_price']}\n";
            echo "Base price: {$result['base_price']}\n";
            echo "Brewing time: {$result['brewing_time_seconds']} seconds\n";
            echo "Barista fee: {$result['barista_fee_percent']}% = {$result['barista_fee']}\n";
            echo "Total price: {$result['total_price']}\n";
            echo "Max allowed: {$coffeeService->getMaxPrice()}\n";
            echo str_repeat("-", 40) . "\n";
            
        } catch (Exception $e) {
            echo "ERROR: {$e->getMessage()}\n";
            echo str_repeat("-", 40) . "\n";
        }
    }
}

echo "\n=== Price Analysis ===\n";
echo "Maximum possible price combinations:\n";

// Найдем максимальную цену
$maxPrice = 0;
$maxCombination = null;

foreach ($beanTypes as $beans) {
    foreach ($milkTypes as $milk) {
        $result = $coffeeService->brewCoffee($beans, $milk);
        if ($result['total_price'] > $maxPrice) {
            $maxPrice = $result['total_price'];
            $maxCombination = $result;
        }
    }
}

echo "Highest price combination: {$maxCombination['beans']} + {$maxCombination['milk']}\n";
echo "Price: {$maxCombination['total_price']}\n";
echo "Is under limit: " . ($maxCombination['total_price'] <= $coffeeService->getMaxPrice() ? "YES" : "NO") . "\n"; 