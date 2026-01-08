"""
FeuerBird Exokernel - Conan 2 Package Recipe

This recipe provides reproducible builds for the FeuerBird Exokernel project.
Use `conan lock create .` to generate a lockfile for reproducibility.
"""

from conan import ConanFile
from conan.tools.cmake import CMakeToolchain, CMake, cmake_layout
from conan.tools.files import copy
import os


class FeuerBirdExokernelConan(ConanFile):
    name = "feuerbird-exokernel"
    version = "1.0.0"
    license = "MIT"
    author = "FeuerBird Project"
    url = "https://github.com/Oichkatzelesfrettschen/feuerbird_exokernel"
    description = "Exokernel OS with POSIX 2024 compliance, capability-based security, and multi-personality Unix compatibility"
    topics = ("exokernel", "operating-system", "posix", "capability-security", "libos")

    # Build settings
    settings = "os", "compiler", "build_type", "arch"

    # Build options
    options = {
        "shared": [True, False],
        "fPIC": [True, False],
        "use_capnp": [True, False],
        "use_ticket_lock": [True, False],
        "use_simd": [True, False],
        "ipc_debug": [True, False],
        "use_lto": [True, False],
        "use_lld": [True, False],
    }
    default_options = {
        "shared": False,
        "fPIC": True,
        "use_capnp": False,
        "use_ticket_lock": False,
        "use_simd": True,
        "ipc_debug": False,
        "use_lto": False,
        "use_lld": True,
    }

    # Conan 2 generators
    generators = "CMakeDeps"

    # Source files to export
    exports_sources = (
        "CMakeLists.txt",
        "cmake/*",
        "kernel/*",
        "libos/*",
        "user/*",
        "include/*",
        "src/*",
        "proto/*",
        "tests/*",
        "demos/*",
        "tools/*",
    )

    def requirements(self):
        """Optional dependencies - uncomment to enable."""
        # Cap'n Proto for serialization (optional)
        if self.options.use_capnp:
            self.requires("capnproto/1.0.1")

    def build_requirements(self):
        """Build-time dependencies."""
        # Ninja generator (optional but recommended)
        self.tool_requires("ninja/1.12.1")

    def config_options(self):
        """Configure options based on platform."""
        if self.settings.os == "Windows":
            del self.options.fPIC

    def configure(self):
        """Configure recipe based on settings."""
        if self.options.shared:
            self.options.rm_safe("fPIC")

    def layout(self):
        """Define the build layout."""
        cmake_layout(self)

    def generate(self):
        """Generate build system files."""
        tc = CMakeToolchain(self)

        # Pass options to CMake
        tc.variables["USE_CAPNP"] = self.options.use_capnp
        tc.variables["USE_TICKET_LOCK"] = self.options.use_ticket_lock
        tc.variables["USE_SIMD"] = self.options.use_simd
        tc.variables["IPC_DEBUG"] = self.options.ipc_debug
        tc.variables["USE_LTO"] = self.options.use_lto
        tc.variables["USE_LLD"] = self.options.use_lld

        # Kernel-specific settings
        tc.variables["CMAKE_EXPORT_COMPILE_COMMANDS"] = True

        tc.generate()

    def build(self):
        """Build the project."""
        cmake = CMake(self)
        cmake.configure()
        cmake.build()

    def package(self):
        """Package the built artifacts."""
        cmake = CMake(self)
        cmake.install()

        # Copy headers
        copy(self, "*.h",
             src=os.path.join(self.source_folder, "include"),
             dst=os.path.join(self.package_folder, "include"))

        # Copy kernel binary
        copy(self, "kernel",
             src=os.path.join(self.build_folder, "kernel"),
             dst=os.path.join(self.package_folder, "bin"))

        # Copy license
        copy(self, "LICENSE",
             src=self.source_folder,
             dst=os.path.join(self.package_folder, "licenses"))

    def package_info(self):
        """Provide package information for consumers."""
        self.cpp_info.set_property("cmake_file_name", "FeuerBirdExokernel")
        self.cpp_info.set_property("cmake_target_name", "feuerbird::exokernel")

        # Include directories
        self.cpp_info.includedirs = ["include"]

        # Binary directory
        self.cpp_info.bindirs = ["bin"]
