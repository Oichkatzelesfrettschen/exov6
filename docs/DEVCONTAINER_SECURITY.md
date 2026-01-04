# FeuerBird Exokernel - Dev Container Security & Supply Chain

**Version:** 2.0  
**Last Updated:** 2026-01-04  
**Security Level:** Hardened

---

## Overview

This document describes the security measures implemented in the development container to protect against supply chain attacks and ensure reproducible, verifiable builds.

---

## Security Measures

### 1. Checksum Verification

All downloaded binaries are verified using SHA-256 checksums before installation:

```dockerfile
# Example: Z3 with checksum
Z3_SHA256=9f58f3710bd2094085951a75791550f547903d75fe7e2fcb373c5f03fc761b8f
wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-glibc-2.35.zip
echo "${Z3_SHA256}  z3-${Z3_VERSION}-x64-glibc-2.35.zip" | sha256sum -c -
```

**Benefits:**
- Detects corrupted downloads
- Prevents man-in-the-middle attacks
- Ensures file integrity

### 2. Version Pinning

All tools use explicit version numbers stored in variables:

```dockerfile
Z3_VERSION=4.12.2
TLA_VERSION=1.8.0
INFER_VERSION=1.1.0
```

**Benefits:**
- Reproducible builds
- Explicit control over upgrades
- Easy audit trail

### 3. Git Commit Pinning

For Git-cloned repositories, specific commit SHAs are used:

```dockerfile
FLAMEGRAPH_COMMIT=cd9ee4c4449775a2f867acf31c84b7fe4b132ad5
git clone https://github.com/brendangregg/FlameGraph /opt/flamegraph
cd /opt/flamegraph && git checkout ${FLAMEGRAPH_COMMIT}
```

**Benefits:**
- Immutable references
- Protection against repository tampering
- Verifiable source code

### 4. HTTPS Downloads

All downloads use HTTPS with certificate verification:

```dockerfile
wget https://github.com/...  # Uses system CA certificates
```

**Benefits:**
- Encrypted transport
- Server authentication
- Prevention of downgrade attacks

---

## Verified Tools & Checksums

### Z3 Theorem Prover

- **Version:** 4.12.2
- **URL:** https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.35.zip
- **SHA-256:** `9f58f3710bd2094085951a75791550f547903d75fe7e2fcb373c5f03fc761b8f`
- **Verification Date:** 2026-01-04
- **Source:** Official GitHub releases

### TLA+ Tools

- **Version:** 1.8.0
- **URL:** https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
- **SHA-256:** `99b8ac649829a0b19f3990a1d32a5dfc8de2f5f85ff3de2a05c0f9b3c5dabb61`
- **Verification Date:** 2026-01-04
- **Source:** Official GitHub releases

### FlameGraph

- **Commit:** cd9ee4c4449775a2f867acf31c84b7fe4b132ad5
- **URL:** https://github.com/brendangregg/FlameGraph
- **Verification Date:** 2026-01-04
- **Source:** Official repository (Brendan Gregg)

### Facebook Infer

- **Version:** 1.1.0
- **URL:** https://github.com/facebook/infer/releases/download/v1.1.0/infer-linux64-v1.1.0.tar.xz
- **SHA-256:** `2f850e794d9f7bc87c3c9a827d85f5e5e88bb2e6088c4f05a9b3a69a96e3f6a5`
- **Verification Date:** 2026-01-04
- **Source:** Official GitHub releases

---

## Checksum Verification Process

### How to Verify Checksums

When updating tool versions, follow this process:

1. **Download the file:**
   ```bash
   wget https://github.com/.../tool.tar.gz
   ```

2. **Calculate SHA-256:**
   ```bash
   sha256sum tool.tar.gz
   ```

3. **Verify against official sources:**
   - Check release page
   - Compare with published checksums
   - Verify signature if available

4. **Update Dockerfile:**
   ```dockerfile
   TOOL_SHA256=<calculated_checksum>
   ```

### Official Checksum Sources

- **Z3:** Checksums on GitHub releases page
- **TLA+:** JAR integrity verifiable via Java manifest
- **Infer:** Checksums on GitHub releases page
- **FlameGraph:** Git commit SHA serves as integrity check

---

## Supply Chain Security Best Practices

### 1. Least Privilege

Build containers run as non-root user (`vscode`) after installation:

```dockerfile
USER vscode
WORKDIR /workspace
```

### 2. Immutable Base Image

Base image pinned to specific tag:

```dockerfile
FROM ubuntu:24.04  # Consider using digest: ubuntu@sha256:...
```

**Recommendation:** Use image digest for maximum security:
```dockerfile
FROM ubuntu@sha256:ab3f5c7a....
```

### 3. Multi-Stage Builds

Consider separating build-time and runtime dependencies:

```dockerfile
FROM ubuntu:24.04 AS builder
# Download and verify tools
...

FROM ubuntu:24.04
# Copy only verified binaries
COPY --from=builder /usr/local/bin/ /usr/local/bin/
```

### 4. Transparency Logs

All downloads logged in build output:

```
Step X/Y : RUN wget ...
--2026-01-04 12:34:56--  https://github.com/...
Resolving github.com... 140.82.113.4
Connecting to github.com|140.82.113.4|:443... connected.
HTTP request sent, awaiting response... 200 OK
```

---

## Update Process

### Updating Tool Versions

1. **Check for new release:**
   ```bash
   # Example: Z3
   curl -s https://api.github.com/repos/Z3Prover/z3/releases/latest | jq -r .tag_name
   ```

2. **Download new version:**
   ```bash
   wget https://github.com/Z3Prover/z3/releases/download/z3-X.Y.Z/z3-X.Y.Z-x64-glibc-2.35.zip
   ```

3. **Calculate checksum:**
   ```bash
   sha256sum z3-X.Y.Z-x64-glibc-2.35.zip
   ```

4. **Update Dockerfile:**
   ```dockerfile
   Z3_VERSION=X.Y.Z
   Z3_SHA256=<new_checksum>
   ```

5. **Test build:**
   ```bash
   docker build -f .devcontainer/Dockerfile .
   ```

6. **Commit changes:**
   ```bash
   git commit -m "Update Z3 to vX.Y.Z with verified checksum"
   ```

### Updating Git-Based Tools

1. **Find latest stable commit:**
   ```bash
   git ls-remote https://github.com/brendangregg/FlameGraph HEAD
   ```

2. **Update Dockerfile:**
   ```dockerfile
   FLAMEGRAPH_COMMIT=<new_commit_sha>
   ```

3. **Test and commit**

---

## Security Audit Log

### 2026-01-04: Initial Security Hardening

**Changes:**
- ✅ Added SHA-256 verification for Z3
- ✅ Added SHA-256 verification for TLA+ tools
- ✅ Added SHA-256 verification for Infer
- ✅ Pinned FlameGraph to specific commit
- ✅ Implemented version variables for maintainability

**Risk Assessment:**
- Before: High risk (no verification)
- After: Low risk (verified checksums, pinned versions)

**Validation:**
- All checksums verified against official sources
- Build tested successfully
- No functionality regressions

---

## Threat Model

### Threats Mitigated

1. **Compromised Upstream** ✅
   - Checksum verification prevents malicious binaries
   
2. **Man-in-the-Middle** ✅
   - HTTPS + checksums prevent MITM attacks
   
3. **Tag Manipulation** ✅
   - Commit pinning prevents tag rewriting
   
4. **Typosquatting** ✅
   - Explicit URLs prevent domain typos

### Residual Risks

1. **Compromised Official Repository** ⚠️
   - Requires official repository compromise + checksum update
   - Mitigation: Code review of Dockerfile changes
   
2. **Base Image Vulnerabilities** ⚠️
   - Ubuntu 24.04 base image
   - Mitigation: Regular updates, vulnerability scanning

3. **Build-Time Attacks** ⚠️
   - Malicious build environment
   - Mitigation: Use trusted CI/CD infrastructure

---

## Compliance & Standards

### SLSA Framework

Supply-chain Levels for Software Artifacts (SLSA):

- **Level 1:** ✅ Build process documented
- **Level 2:** ✅ Checksums verified
- **Level 3:** 🔄 Could add signed provenance
- **Level 4:** ⚠️ Requires hermetic builds

### NIST Guidelines

Aligned with NIST SP 800-218 (Secure Software Development Framework):

- ✅ PW.1.1: Use secure communication protocols
- ✅ PW.4.1: Verify third-party components
- ✅ PW.4.4: Use pinned versions
- ✅ PW.7.1: Document security measures

---

## Verification Commands

### Verify Dockerfile Security

```bash
# Check for pinned versions
grep -E "VERSION=|COMMIT=|SHA256=" .devcontainer/Dockerfile

# Check for checksum verification
grep "sha256sum -c" .devcontainer/Dockerfile

# Check for HTTPS usage
grep "wget https://" .devcontainer/Dockerfile
```

### Build with Extra Verification

```bash
# Build with verbose output
docker build --no-cache --progress=plain -f .devcontainer/Dockerfile .

# Inspect final image
docker run --rm <image_id> sha256sum /usr/local/bin/z3
docker run --rm <image_id> sha256sum /usr/local/bin/tla2tools.jar
```

---

## References

### Security Standards
- [SLSA Framework](https://slsa.dev/)
- [NIST SSDF](https://csrc.nist.gov/publications/detail/sp/800-218/final)
- [Docker Security Best Practices](https://docs.docker.com/develop/security-best-practices/)
- [GitHub Actions Security Hardening](https://docs.github.com/en/actions/security-guides/security-hardening-for-github-actions)

### Tool Documentation
- [Z3 Releases](https://github.com/Z3Prover/z3/releases)
- [TLA+ Releases](https://github.com/tlaplus/tlaplus/releases)
- [FlameGraph Repository](https://github.com/brendangregg/FlameGraph)
- [Infer Releases](https://github.com/facebook/infer/releases)

---

## Maintenance Schedule

- **Weekly:** Check for security advisories
- **Monthly:** Review tool versions
- **Quarterly:** Update to latest stable versions
- **Annually:** Full security audit

---

**Document Status:** ✅ Active  
**Next Review:** 2026-04-04  
**Owner:** Development Team  
**Classification:** Public
