<?php

namespace App\Invoice;

class Invoice
{
    private float $price;

    public function __construct(float $price)
    {
        if ($price < 0) {
            throw new \InvalidArgumentException('Price cannot be negative');
        }
        $this->price = $price;
    }

    public function getPrice(): float
    {
        return $this->price;
    }

    public function setPrice(float $price): void
    {
        if ($price < 0) {
            throw new \InvalidArgumentException('Price cannot be negative');
        }
        $this->price = $price;
    }
} 