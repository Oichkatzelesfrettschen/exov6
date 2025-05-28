posix_tests = files('../../src/engine/user/posix_file_test.c',
                    '../../src/engine/user/posix_signal_test.c',
                    '../../src/engine/user/posix_pipe_test.c',
                    '../../src/engine/user/posix_rename_unlink_test.c',
                    '../../src/engine/user/demos/posix_misc_test.c',
                    '../../src/engine/user/demos/posix_socket_test.c',
                    '../../src/engine/user/demos/posix_cwd_test.c')
libos_srcs = files('../../src/engine/libos/posix.c',
                   '../../src/engine/libos/fs.c',
                   '../../src/engine/libos/file.c',
                   '../../src/engine/libos/fs_ufs.c',
                   '../../tests/libos_host_stubs.c')
foreach src : posix_tests
  exe_name = src.stem()
  executable(exe_name, [src] + libos_srcs,
             include_directories: include_directories('../../',
                                                    '../../src/engine/include',
                                                    '../../src/engine/libos/include',
                                                    '../../tests/include'),
             install: false)
endforeach
