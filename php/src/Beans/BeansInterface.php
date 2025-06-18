<?php

namespace Coffee\Beans;

interface BeansInterface
{
    public function getPrice(): float;
    public function getBrewingTimeSeconds(): int;
    public function getName(): string;
} 