posix_tests = files('../../user/posix_file_test.c',
                    '../../user/posix_signal_test.c',
                    '../../user/posix_pipe_test.c',
                    '../../user/posix_rename_unlink_test.c',
                    '../../examples/demos/posix_misc_test.c',
                    '../../examples/demos/posix_socket_test.c',
                    '../../examples/demos/posix_cwd_test.c')
libos_srcs = files('../../libos/posix.c',
                   '../../libos/fs.c',
                   '../../libos/file.c',
                   '../../libos/fs_ufs.c',
                   '../../tests/libos_host_stubs.c')
foreach src : posix_tests
  exe_name = src.stem()
  executable(exe_name, [src] + libos_srcs,
             include_directories: include_directories('../../',
                                                    '../../include',
                                                    '../../libos/include',
                                                    '../../tests/include'),
             install: false)
endforeach
