<?php

declare(strict_types=1);

namespace Yaroslam\Phpisabelle\Entity;

class Role
{
    private int $id;
    private string $name;
    private string $description;
    private array $permissions;

    public function __construct(int $id, string $name, string $description = '', array $permissions = [])
    {
        $this->id = $id;
        $this->name = $name;
        $this->description = $description;
        $this->permissions = $permissions;
    }

    public function getId(): int
    {
        return $this->id;
    }

    public function getName(): string
    {
        return $this->name;
    }

    public function setName(string $name): void
    {
        if (empty(trim($name))) {
            throw new \InvalidArgumentException('Role name cannot be empty');
        }
        $this->name = trim($name);
    }

    public function getDescription(): string
    {
        return $this->description;
    }

    public function setDescription(string $description): void
    {
        $this->description = $description;
    }

    public function getPermissions(): array
    {
        return $this->permissions;
    }

    public function addPermission(string $permission): void
    {
        if (!in_array($permission, $this->permissions, true)) {
            $this->permissions[] = $permission;
        }
    }

    public function removePermission(string $permission): void
    {
        $key = array_search($permission, $this->permissions, true);
        if ($key !== false) {
            unset($this->permissions[$key]);
            $this->permissions = array_values($this->permissions);
        }
    }

    public function hasPermission(string $permission): bool
    {
        return in_array($permission, $this->permissions, true);
    }

    public function toArray(): array
    {
        return [
            'id' => $this->id,
            'name' => $this->name,
            'description' => $this->description,
            'permissions' => $this->permissions,
        ];
    }
} 