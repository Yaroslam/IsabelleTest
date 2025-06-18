<?php

namespace Coffee\Milk;

class AlmondMilk implements MilkInterface
{
    private float $price = 25.0;
    
    public function getPrice(): float
    {
        return $this->price;
    }
    
    public function getName(): string
    {
        return 'Almond Milk';
    }
} 