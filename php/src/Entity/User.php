<?php

declare(strict_types=1);

namespace Yaroslam\Phpisabelle\Entity;

use DateTime;

class User
{
    private int $id;
    private string $email;
    private string $name;
    private DateTime $createdAt;
    private bool $isActive;

    public function __construct(int $id, string $email, string $name, bool $isActive = true)
    {
        $this->id = $id;
        $this->email = $email;
        $this->name = $name;
        $this->isActive = $isActive;
        $this->createdAt = new DateTime();
    }

    public function getId(): int
    {
        return $this->id;
    }

    public function getEmail(): string
    {
        return $this->email;
    }

    public function setEmail(string $email): void
    {
        if (!filter_var($email, FILTER_VALIDATE_EMAIL)) {
            throw new \InvalidArgumentException('Invalid email format');
        }
        $this->email = $email;
    }

    public function getName(): string
    {
        return $this->name;
    }

    public function setName(string $name): void
    {
        if (empty(trim($name))) {
            throw new \InvalidArgumentException('Name cannot be empty');
        }
        $this->name = trim($name);
    }

    public function getCreatedAt(): DateTime
    {
        return $this->createdAt;
    }

    public function isActive(): bool
    {
        return $this->isActive;
    }

    public function activate(): void
    {
        $this->isActive = true;
    }

    public function deactivate(): void
    {
        $this->isActive = false;
    }

    public function toArray(): array
    {
        return [
            'id' => $this->id,
            'email' => $this->email,
            'name' => $this->name,
            'created_at' => $this->createdAt->format('Y-m-d H:i:s'),
            'is_active' => $this->isActive,
        ];
    }
} 