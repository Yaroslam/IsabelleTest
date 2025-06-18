<?php

namespace Coffee\Beans;

class ArabicaBeans implements BeansInterface
{
    private float $price = 45.0;
    private int $brewingTimeSeconds = 120;
    
    public function getPrice(): float
    {
        return $this->price;
    }
    
    public function getBrewingTimeSeconds(): int
    {
        return $this->brewingTimeSeconds;
    }
    
    public function getName(): string
    {
        return 'Arabica';
    }
} 