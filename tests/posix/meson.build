posix_tests = files('../../src-uland/posix_file_test.c',
                    '../../src-uland/posix_signal_test.c',
                    '../../src-uland/posix_pipe_test.c',
                    '../../src-uland/user/posix_misc_test.c',
                    '../../src-uland/user/posix_socket_test.c')
libos_srcs = files('../../libos/posix.c',
                   '../../libos/fs.c',
                   '../../libos/file.c',
                   '../../libos/fs_ufs.c',
                   '../../tests/libos_host_stubs.c')
foreach src : posix_tests
  exe_name = src.stem()
  executable(exe_name, [src] + libos_srcs,
             include_directories: include_directories('../../',
                                                    '../../src-headers',
                                                    '../../libos/include',
                                                    '../../tests/include'),
             install: false)
endforeach
