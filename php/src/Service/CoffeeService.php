<?php

namespace Coffee\Service;

use Coffee\Beans\BeansInterface;
use Coffee\Milk\MilkInterface;

class CoffeeService
{
    private const MAX_PRICE = 100.0;
    private const BASE_BARISTA_FEE = 5.0;
    
    public function brewCoffee(BeansInterface $beans, MilkInterface $milk): array
    {
        $beansPrice = $beans->getPrice();
        $milkPrice = $milk->getPrice();
        $brewingTime = $beans->getBrewingTimeSeconds();
        
        // Базовая цена = цена зерен + цена молока
        $basePrice = $beansPrice + $milkPrice;
        
        // Надбавка бариста = 5.xxx% где xxx - секунды варки
        $baristaFeePercent = self::BASE_BARISTA_FEE + ($brewingTime / 1000);
        $baristaFee = $basePrice * ($baristaFeePercent / 100);
        
        // Итоговая цена
        $totalPrice = $basePrice + $baristaFee;
        
        // Проверка максимальной цены
        if ($totalPrice > self::MAX_PRICE) {
            throw new \Exception("Coffee price exceeds maximum allowed price of " . self::MAX_PRICE);
        }
        
        return [
            'beans' => $beans->getName(),
            'milk' => $milk->getName(),
            'beans_price' => $beansPrice,
            'milk_price' => $milkPrice,
            'base_price' => $basePrice,
            'brewing_time_seconds' => $brewingTime,
            'barista_fee_percent' => round($baristaFeePercent, 3),
            'barista_fee' => round($baristaFee, 2),
            'total_price' => round($totalPrice, 2)
        ];
    }
    
    public function getMaxPrice(): float
    {
        return self::MAX_PRICE;
    }
} 