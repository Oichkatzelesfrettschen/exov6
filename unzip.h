#ifndef UNZIP_H
#define UNZIP_H
#include "zlib.h"
#ifdef __cplusplus
extern "C" {
#endif

typedef voidpf unzFile;

typedef struct tm_unz_s {
    uInt tm_sec;
    uInt tm_min;
    uInt tm_hour;
    uInt tm_mday;
    uInt tm_mon;
    uInt tm_year;
} tm_unz;

typedef struct unz_global_info_s {
    uLong number_entry;
    uLong size_comment;
} unz_global_info;

typedef struct unz_file_info_s {
    uLong version;
    uLong version_needed;
    uLong flag;
    uLong compression_method;
    uLong dosDate;
    uLong crc;
    uLong compressed_size;
    uLong uncompressed_size;
    uLong size_filename;
    uLong size_file_extra;
    uLong size_file_comment;
    uLong disk_num_start;
    uLong internal_fa;
    uLong external_fa;
    tm_unz tmu_date;
} unz_file_info;

typedef struct unz_file_pos_s {
    uLong pos_in_zip_directory;
    uLong num_of_file;
} unz_file_pos;

struct zlib_filefunc_def_s; /* forward declaration */
typedef struct zlib_filefunc_def_s zlib_filefunc_def;

int unzStringFileNameCompare(const char* fileName1, const char* fileName2, int iCaseSensitivity);
unzFile unzOpen(const char *path);
unzFile unzOpen2(const char *path, zlib_filefunc_def* pzlib_filefunc_def);
int unzClose(unzFile file);
int unzGetGlobalInfo(unzFile file, unz_global_info *pglobal_info);
int unzGetGlobalComment(unzFile file, char *szComment, uLong uSizeBuf);
int unzGoToFirstFile(unzFile file);
int unzGoToNextFile(unzFile file);
int unzLocateFile(unzFile file, const char *szFileName, int iCaseSensitivity);
int unzGetFilePos(unzFile file, unz_file_pos* file_pos);
int unzGoToFilePos(unzFile file, unz_file_pos* file_pos);
int unzGetCurrentFileInfo(unzFile file, unz_file_info *pfile_info,
                          char *szFileName, uLong fileNameBufferSize,
                          void *extraField, uLong extraFieldBufferSize,
                          char *szComment, uLong commentBufferSize);
int unzOpenCurrentFile(unzFile file);
int unzOpenCurrentFilePassword(unzFile file, const char* password);
int unzOpenCurrentFile2(unzFile file, int* method, int* level, int raw);
int unzOpenCurrentFile3(unzFile file, int* method, int* level, int raw, const char* password);
int unzReadCurrentFile(unzFile file, voidp buf, unsigned len);
z_off_t unztell(unzFile file);
int unzeof(unzFile file);
int unzGetLocalExtrafield(unzFile file, voidp buf, unsigned len);
int unzCloseCurrentFile(unzFile file);
uLong unzGetOffset(unzFile file);
int unzSetOffset(unzFile file, uLong pos);

#ifdef __cplusplus
}
#endif
#endif /* UNZIP_H */
