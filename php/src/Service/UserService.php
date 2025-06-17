<?php

declare(strict_types=1);

namespace Yaroslam\Phpisabelle\Service;

use Yaroslam\Phpisabelle\Entity\User;
use Yaroslam\Phpisabelle\Repository\UserRepositoryInterface;
use Yaroslam\Phpisabelle\Exception\UserNotFoundException;
use Yaroslam\Phpisabelle\Exception\UserAlreadyExistsException;

class UserService
{
    private UserRepositoryInterface $userRepository;

    public function __construct(UserRepositoryInterface $userRepository)
    {
        $this->userRepository = $userRepository;
    }

    public function createUser(string $email, string $name): User
    {
        if ($this->userRepository->findByEmail($email) !== null) {
            throw new UserAlreadyExistsException("User with email '{$email}' already exists");
        }

        $user = new User(0, $email, $name);
        $this->userRepository->save($user);
        
        return $user;
    }

    public function getUserById(int $id): User
    {
        $user = $this->userRepository->findById($id);
        if ($user === null) {
            throw new UserNotFoundException("User with ID {$id} not found");
        }
        
        return $user;
    }

    public function getUserByEmail(string $email): User
    {
        $user = $this->userRepository->findByEmail($email);
        if ($user === null) {
            throw new UserNotFoundException("User with email '{$email}' not found");
        }
        
        return $user;
    }

    public function updateUser(int $id, ?string $email = null, ?string $name = null): User
    {
        $user = $this->getUserById($id);

        if ($email !== null && $email !== $user->getEmail()) {
            if ($this->userRepository->findByEmail($email) !== null) {
                throw new UserAlreadyExistsException("User with email '{$email}' already exists");
            }
            $user->setEmail($email);
        }

        if ($name !== null) {
            $user->setName($name);
        }

        $this->userRepository->save($user);
        
        return $user;
    }

    public function deleteUser(int $id): bool
    {
        $user = $this->getUserById($id);
        return $this->userRepository->delete($id);
    }

    public function activateUser(int $id): User
    {
        $user = $this->getUserById($id);
        $user->activate();
        $this->userRepository->save($user);
        
        return $user;
    }

    public function deactivateUser(int $id): User
    {
        $user = $this->getUserById($id);
        $user->deactivate();
        $this->userRepository->save($user);
        
        return $user;
    }

    public function getAllUsers(): array
    {
        return $this->userRepository->findAll();
    }

    public function getActiveUsers(): array
    {
        return array_values($this->userRepository->findActiveUsers());
    }

    public function getUsersCount(): int
    {
        return count($this->userRepository->findAll());
    }

    public function getActiveUsersCount(): int
    {
        return count($this->userRepository->findActiveUsers());
    }
} 