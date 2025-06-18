<?php

namespace Coffee\Beans;

class RobustaBeans implements BeansInterface
{
    private float $price = 30.0;
    private int $brewingTimeSeconds = 90;
    
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
        return 'Robusta';
    }
} 