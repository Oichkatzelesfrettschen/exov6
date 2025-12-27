#!/bin/bash
# Script to reorganize codebase by license type
# This creates the proper directory structure and moves files accordingly

set -e

echo "=== FeuerBird License-Based Restructuring Script ==="
echo "This script will reorganize the codebase by license type"
echo

# Create new directory structure
echo "Creating license-based directory structure..."
mkdir -p bsd/{kernel,libos,user,include}
mkdir -p gpl/{ddekit,rump,drivers}
mkdir -p mit/{tools,libs}
mkdir -p limine
mkdir -p llvm-libc++

# Function to detect license in file
detect_license() {
    local file="$1"
    if grep -q "GPL\|General Public License" "$file" 2>/dev/null; then
        echo "GPL"
    elif grep -q "BSD\|Berkeley Software Distribution" "$file" 2>/dev/null; then
        echo "BSD"
    elif grep -q "MIT License\|MIT license" "$file" 2>/dev/null; then
        echo "MIT"
    elif grep -q "Apache\|APACHE" "$file" 2>/dev/null; then
        echo "Apache"
    else
        # Default to BSD for original feuerbird code
        echo "BSD"
    fi
}

# Function to move file preserving directory structure
move_file_by_license() {
    local file="$1"
    local license=$(detect_license "$file")
    local dest_base=""
    
    case "$license" in
        GPL)
            dest_base="gpl"
            ;;
        BSD)
            dest_base="bsd"
            ;;
        MIT)
            dest_base="mit"
            ;;
        Apache)
            # Skip Apache files (will be in llvm-libc++)
            return
            ;;
        *)
            dest_base="bsd"  # Default
            ;;
    esac
    
    # Determine subdirectory based on original location
    if [[ "$file" == kernel/* ]]; then
        dest="$dest_base/kernel/"
    elif [[ "$file" == libos/* ]]; then
        dest="$dest_base/libos/"
    elif [[ "$file" == user/* ]]; then
        dest="$dest_base/user/"
    elif [[ "$file" == include/* ]]; then
        dest="$dest_base/include/"
    else
        dest="$dest_base/"
    fi
    
    echo "  $file -> $dest (License: $license)"
    # Uncomment to actually move files
    # mkdir -p "$dest"
    # git mv "$file" "$dest" 2>/dev/null || mv "$file" "$dest"
}

# Analyze kernel files
echo
echo "Analyzing kernel files..."
for file in kernel/*.c kernel/*.h; do
    [ -f "$file" ] && move_file_by_license "$file"
done

# Analyze libos files
echo
echo "Analyzing libos files..."
for file in libos/*.c libos/*.h; do
    [ -f "$file" ] && move_file_by_license "$file"
done

# Analyze user files
echo
echo "Analyzing user files..."
for file in user/*.c user/*.h; do
    [ -f "$file" ] && move_file_by_license "$file"
done

# Special handling for known GPL components
echo
echo "Moving known GPL components..."
if [ -d "src/ddekit" ]; then
    echo "  src/ddekit -> gpl/ddekit"
    # git mv src/ddekit gpl/
fi

# Create license summary
echo
echo "Creating LICENSE_MAP.md..."
cat > LICENSE_MAP.md << 'EOF'
# License Organization Map

## Directory Structure by License

### BSD License (`bsd/`)
- Original FeuerBird code
- Core kernel components
- Basic POSIX utilities
- LibOS POSIX layer

### GPL License (`gpl/`)
- DDE Kit (Device Driver Environment)
- Rump kernel components
- GPL device drivers

### MIT License (`mit/`)
- Supporting tools
- Build utilities
- Testing frameworks

### Apache 2.0 License (`llvm-libc++/`)
- LLVM libc++ runtime
- C++23 standard library
- Compiler runtime support

### Limine Bootloader (`limine/`)
- 2-clause BSD license
- Separate build and link

## Migration Status

- [ ] Kernel files analyzed and moved
- [ ] LibOS files analyzed and moved
- [ ] User utilities analyzed and moved
- [ ] DDE Kit isolated to GPL directory
- [ ] Rump kernel isolated to GPL directory
- [ ] Build system updated for new structure
- [ ] Git history preserved with moves

## Build Integration

Each license directory maintains its own build configuration:
- `bsd/meson.build` - BSD components
- `gpl/meson.build` - GPL components (optional)
- `mit/meson.build` - MIT components
- `llvm-libc++/CMakeLists.txt` - LLVM build

The main build system combines outputs while respecting license boundaries.
EOF

echo
echo "=== Analysis Complete ==="
echo "Review the proposed changes above."
echo "To execute the restructuring, uncomment the move commands in this script."
echo "See LICENSE_MAP.md for the organization summary."