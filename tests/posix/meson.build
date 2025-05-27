posix_tests = files('../../engine/user/posix_file_test.c',
                    '../../engine/user/posix_signal_test.c',
                    '../../engine/user/posix_pipe_test.c',
                    '../../engine/user/posix_rename_unlink_test.c',
                    '../../engine/user/demos/posix_misc_test.c',
                    '../../engine/user/demos/posix_socket_test.c',
                    '../../engine/user/demos/posix_cwd_test.c')
libos_srcs = files('../../engine/libos/posix.c',
                   '../../engine/libos/fs.c',
                   '../../engine/libos/file.c',
                   '../../engine/libos/fs_ufs.c',
                   '../../tests/libos_host_stubs.c')
foreach src : posix_tests
  exe_name = src.stem()
  executable(exe_name, [src] + libos_srcs,
             include_directories: include_directories('../../',
                                                    '../../engine/include',
                                                    '../../engine/libos/include',
                                                    '../../tests/include'),
             install: false)
endforeach
