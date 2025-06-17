<?php

declare(strict_types=1);

namespace Yaroslam\Phpisabelle\Repository;

use Yaroslam\Phpisabelle\Entity\User;

class InMemoryUserRepository implements UserRepositoryInterface
{
    private array $users = [];
    private int $nextId = 1;

    public function __construct()
    {
        // Добавляем несколько тестовых пользователей
        $this->save(new User(1, 'admin@example.com', 'Administrator', true));
        $this->save(new User(2, 'user@example.com', 'Regular User', true));
        $this->save(new User(3, 'inactive@example.com', 'Inactive User', false));
        $this->nextId = 4;
    }

    public function findById(int $id): ?User
    {
        return $this->users[$id] ?? null;
    }

    public function findByEmail(string $email): ?User
    {
        foreach ($this->users as $user) {
            if ($user->getEmail() === $email) {
                return $user;
            }
        }
        return null;
    }

    public function findAll(): array
    {
        return array_values($this->users);
    }

    public function save(User $user): void
    {
        if ($user->getId() === 0) {
            // Создаем нового пользователя с новым ID
            $this->users[$user->getId()] = $user;
        } else {
            // Обновляем существующего пользователя
            $this->users[$user->getId()] = $user;
        }
    }

    public function delete(int $id): bool
    {
        if (isset($this->users[$id])) {
            unset($this->users[$id]);
            return true;
        }
        return false;
    }

    public function findActiveUsers(): array
    {
        return array_filter($this->users, fn(User $user) => $user->isActive());
    }
} 