<?php

namespace Coffee\Milk;

class WholeMilk implements MilkInterface
{
    private float $price = 15.0;
    
    public function getPrice(): float
    {
        return $this->price;
    }
    
    public function getName(): string
    {
        return 'Whole Milk';
    }
} 