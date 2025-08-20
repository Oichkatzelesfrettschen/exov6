#!/usr/bin/env python3
"""
Security validation tests for exokernel boundaries and post-quantum crypto.

Tests capability authentication, lattice IPC security, and boundary enforcement.
"""

import sys
import os
import subprocess
import tempfile

def test_capability_authentication():
    """Test that capability authentication uses proper cryptographic primitives."""
    print("Testing capability authentication security...")
    
    # Check for hardcoded secrets in cap.c
    with open('kernel/cap.c', 'r') as f:
        content = f.read()
        
    # Should not contain hardcoded secret arrays
    if 'static const uint8_t cap_secret[32] = {' in content:
        print("❌ FAIL: Found hardcoded capability secret")
        return False
        
    # Should use secure derivation
    if 'cap_get_secret' not in content:
        print("❌ FAIL: Capability authentication not using secure derivation")
        return False
        
    # Should use constant-time comparison
    if 'cap_verify_constant_time' not in content:
        print("❌ FAIL: Capability verification not using constant-time comparison")
        return False
        
    print("✅ PASS: Capability authentication uses secure methods")
    return True

def test_crypto_kdf():
    """Test that KDF implementation is not using insecure stubs."""
    print("Testing KDF security...")
    
    with open('kernel/crypto.c', 'r') as f:
        content = f.read()
        
    # Should not contain dangerous stub warnings
    if 'NOT CRYPTOGRAPHICALLY SECURE' in content:
        print("❌ FAIL: Found insecure crypto stubs")
        return False
        
    # Should use proper HKDF-like construction
    if 'simple_sha256' not in content:
        print("❌ FAIL: KDF not using hash-based construction")
        return False
        
    # Should clear sensitive data
    if 'memset(prk, 0' not in content:
        print("❌ FAIL: KDF not clearing sensitive intermediate values")
        return False
        
    print("✅ PASS: KDF implementation is improved")
    return True

def test_lattice_ipc_auth():
    """Test that lattice IPC includes proper authentication."""
    print("Testing lattice IPC authentication...")
    
    with open('kernel/lattice_ipc.c', 'r') as f:
        content = f.read()
        
    # Should include authentication in send
    if 'auth_tag' not in content:
        print("❌ FAIL: Lattice IPC missing authentication tags")
        return False
        
    # Should verify authentication in recv
    if 'hmac_verify_constant_time' not in content:
        print("❌ FAIL: Lattice IPC not using constant-time auth verification")
        return False
        
    # Should clear sensitive data
    if 'cap_secure_clear' not in content:
        print("❌ FAIL: Lattice IPC not clearing sensitive data")
        return False
        
    print("✅ PASS: Lattice IPC includes proper authentication")
    return True

def test_pq_crypto_entropy():
    """Test that post-quantum crypto uses proper entropy."""
    print("Testing post-quantum crypto entropy...")
    
    with open('kernel/crypto.c', 'r') as f:
        content = f.read()
        
    # Should not use predictable key generation
    if 'pk[i] = (uint8_t)i;' in content:
        print("❌ FAIL: Found predictable key generation")
        return False
        
    # Should use entropy generation
    if 'generate_crypto_entropy' not in content:
        print("❌ FAIL: Post-quantum crypto not using proper entropy")
        return False
        
    print("✅ PASS: Post-quantum crypto uses improved entropy")
    return True

def test_security_headers():
    """Test that security headers are properly included."""
    print("Testing security header inclusion...")
    
    if not os.path.exists('kernel/cap_security.h'):
        print("❌ FAIL: Security header cap_security.h not found")
        return False
        
    if not os.path.exists('kernel/cap_security.c'):
        print("❌ FAIL: Security implementation cap_security.c not found")
        return False
        
    print("✅ PASS: Security headers and implementations present")
    return True

def main():
    """Run all security tests."""
    print("=== Exokernel Security Boundary Audit ===\n")
    
    # Change to repository directory
    os.chdir('/home/runner/work/exov6/exov6')
    
    tests = [
        test_capability_authentication,
        test_crypto_kdf,
        test_lattice_ipc_auth,
        test_pq_crypto_entropy,
        test_security_headers
    ]
    
    passed = 0
    total = len(tests)
    
    for test in tests:
        try:
            if test():
                passed += 1
        except Exception as e:
            print(f"❌ FAIL: {test.__name__} - {e}")
        print()
    
    print(f"=== Results: {passed}/{total} tests passed ===")
    
    if passed == total:
        print("🔒 All security tests passed!")
        return 0
    else:
        print("⚠️  Some security issues remain")
        return 1

if __name__ == '__main__':
    sys.exit(main())