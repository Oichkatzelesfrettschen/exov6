/**
 * @file vfs.c
 * @brief Virtual File System Implementation
 */

#include "vfs.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/*******************************************************************************
 * GLOBAL STATE
 ******************************************************************************/

/**
 * @brief Registered filesystem types
 */
typedef struct {
    fs_type_t type;
    const struct vfs_super_operations *s_op;
    const struct vfs_inode_operations *i_op;
    const struct vfs_file_operations *f_op;
} fs_registration_t;

static fs_registration_t g_filesystems[FS_TYPE_MAX];
static struct vfs_mount *g_mounts = NULL;
static bool g_vfs_initialized = false;

/*******************************************************************************
 * INITIALIZATION
 ******************************************************************************/

int vfs_init(void)
{
    if (g_vfs_initialized) {
        return 0;
    }

    memset(g_filesystems, 0, sizeof(g_filesystems));
    g_mounts = NULL;
    g_vfs_initialized = true;

    printf("VFS: Virtual File System initialized\n");
    return 0;
}

int vfs_register_filesystem(fs_type_t type,
                            const struct vfs_super_operations *s_op,
                            const struct vfs_inode_operations *i_op,
                            const struct vfs_file_operations *f_op)
{
    if (!g_vfs_initialized) {
        return -1;
    }

    if (type <= FS_TYPE_NONE || type >= FS_TYPE_MAX) {
        return -1;
    }

    if (!s_op || !i_op || !f_op) {
        return -1;
    }

    /* Check if already registered */
    if (g_filesystems[type].type != FS_TYPE_NONE) {
        return -1;  /* Already registered */
    }

    g_filesystems[type].type = type;
    g_filesystems[type].s_op = s_op;
    g_filesystems[type].i_op = i_op;
    g_filesystems[type].f_op = f_op;

    const char *type_name;
    switch (type) {
        case FS_TYPE_MINIX3: type_name = "MINIX v3"; break;
        case FS_TYPE_EXT4:   type_name = "ext4"; break;
        case FS_TYPE_F2FS:   type_name = "F2FS"; break;
        case FS_TYPE_PROCFS: type_name = "procfs"; break;
        case FS_TYPE_DEVFS:  type_name = "devfs"; break;
        default:             type_name = "unknown"; break;
    }

    printf("VFS: Registered filesystem type: %s\n", type_name);
    return 0;
}

/*******************************************************************************
 * MOUNT MANAGEMENT
 ******************************************************************************/

int vfs_mount(const char *dev, const char *mountpoint,
              fs_type_t fs_type, uint32_t flags)
{
    if (!g_vfs_initialized) {
        return -1;
    }

    if (!dev || !mountpoint) {
        return -1;
    }

    if (fs_type <= FS_TYPE_NONE || fs_type >= FS_TYPE_MAX) {
        return -1;
    }

    /* Check if filesystem is registered */
    if (g_filesystems[fs_type].type == FS_TYPE_NONE) {
        printf("VFS: Filesystem type %d not registered\n", fs_type);
        return -1;
    }

    /* Allocate mount structure */
    struct vfs_mount *mount = malloc(sizeof(struct vfs_mount));
    if (!mount) {
        return -1;
    }

    memset(mount, 0, sizeof(*mount));

    /* Initialize mount */
    strncpy(mount->mountpoint, mountpoint, sizeof(mount->mountpoint) - 1);
    mount->flags = flags;
    atomic_store(&mount->refcount, 1);

    /* Allocate superblock */
    struct vfs_super_block *sb = malloc(sizeof(struct vfs_super_block));
    if (!sb) {
        free(mount);
        return -1;
    }

    memset(sb, 0, sizeof(*sb));

    /* Initialize superblock */
    sb->fs_type = fs_type;
    sb->s_op = g_filesystems[fs_type].s_op;
    sb->i_op = g_filesystems[fs_type].i_op;
    sb->f_op = g_filesystems[fs_type].f_op;
    sb->mount = mount;
    atomic_store(&sb->refcount, 1);

    mount->sb = sb;

    /* Read superblock from device - filesystem-specific */
    /* This would call the filesystem's read_super operation */
    /* For now, this is a stub */

    /* Add to mount list */
    mount->next = g_mounts;
    g_mounts = mount;

    printf("VFS: Mounted %s at %s (type=%d, flags=0x%x)\n",
           dev, mountpoint, fs_type, flags);

    return 0;
}

int vfs_umount(const char *mountpoint)
{
    if (!g_vfs_initialized || !mountpoint) {
        return -1;
    }

    struct vfs_mount **prev = &g_mounts;
    struct vfs_mount *mount = g_mounts;

    /* Find mount point */
    while (mount) {
        if (strcmp(mount->mountpoint, mountpoint) == 0) {
            /* Check if busy */
            if (atomic_load(&mount->refcount) > 1) {
                return -1;  /* Busy */
            }

            /* Remove from list */
            *prev = mount->next;

            /* Sync filesystem */
            if (mount->sb && mount->sb->s_op && mount->sb->s_op->sync_fs) {
                mount->sb->s_op->sync_fs(mount->sb);
            }

            /* Free superblock */
            if (mount->sb) {
                free(mount->sb->fs_private);
                free(mount->sb);
            }

            /* Free mount */
            free(mount);

            printf("VFS: Unmounted %s\n", mountpoint);
            return 0;
        }

        prev = &mount->next;
        mount = mount->next;
    }

    return -1;  /* Not found */
}

/*******************************************************************************
 * PATH LOOKUP
 ******************************************************************************/

struct vfs_inode* vfs_path_lookup(const char *path)
{
    if (!g_vfs_initialized || !path) {
        return NULL;
    }

    /* Handle absolute paths */
    if (path[0] != '/') {
        /* TODO: Support relative paths with current working directory */
        return NULL;
    }

    /* Find mount point */
    struct vfs_mount *best_mount = NULL;
    size_t best_len = 0;

    for (struct vfs_mount *m = g_mounts; m; m = m->next) {
        size_t len = strlen(m->mountpoint);

        /* Check if path starts with this mount point */
        if (strncmp(path, m->mountpoint, len) == 0) {
            /* Check it's a better match */
            if (len > best_len) {
                best_mount = m;
                best_len = len;
            }
        }
    }

    if (!best_mount) {
        return NULL;  /* No mount point found */
    }

    /* Get root inode */
    struct vfs_inode *inode = best_mount->sb->root_inode;
    if (!inode) {
        return NULL;
    }

    /* Skip mount point prefix */
    const char *relpath = path + best_len;
    if (*relpath == '/') {
        relpath++;
    }

    /* If empty, return root */
    if (*relpath == '\0') {
        vfs_inode_get(inode);
        return inode;
    }

    /* Walk path components */
    char component[256];
    while (*relpath) {
        /* Extract next component */
        const char *slash = strchr(relpath, '/');
        uint32_t len;

        if (slash) {
            len = slash - relpath;
            if (len >= sizeof(component)) {
                return NULL;  /* Component too long */
            }
            memcpy(component, relpath, len);
            component[len] = '\0';
            relpath = slash + 1;
        } else {
            len = strlen(relpath);
            if (len >= sizeof(component)) {
                return NULL;
            }
            strcpy(component, relpath);
            relpath += len;
        }

        /* Skip empty components (double slashes) */
        if (len == 0) {
            continue;
        }

        /* Check if inode is a directory */
        if ((inode->mode & 0170000) != 0040000) {  /* S_IFDIR = 0040000 */
            return NULL;  /* Not a directory */
        }

        /* Look up component */
        if (!inode->sb->i_op || !inode->sb->i_op->lookup) {
            return NULL;
        }

        uint64_t inum = inode->sb->i_op->lookup(inode, component, len);
        if (inum == 0) {
            return NULL;  /* Not found */
        }

        /* Read inode */
        if (!inode->sb->s_op || !inode->sb->s_op->read_inode) {
            return NULL;
        }

        struct vfs_inode *next = inode->sb->s_op->read_inode(inode->sb, inum);
        if (!next) {
            return NULL;
        }

        /* Release old inode if not root */
        if (inode != best_mount->sb->root_inode) {
            vfs_inode_put(inode);
        }

        inode = next;
    }

    return inode;
}

/*******************************************************************************
 * INODE REFERENCE COUNTING
 ******************************************************************************/

void vfs_inode_put(struct vfs_inode *inode)
{
    if (!inode) return;

    uint32_t old = atomic_fetch_sub(&inode->refcount, 1);
    if (old == 1) {
        /* Last reference - free inode */

        /* Write back if dirty */
        if ((atomic_load(&inode->state) & VFS_INODE_DIRTY) &&
            inode->sb && inode->sb->s_op && inode->sb->s_op->write_inode) {
            inode->sb->s_op->write_inode(inode);
        }

        /* Destroy inode */
        if (inode->sb && inode->sb->s_op && inode->sb->s_op->destroy_inode) {
            inode->sb->s_op->destroy_inode(inode);
        } else {
            /* Default: free filesystem-specific data and inode */
            free(inode->fs_private);
            free(inode);
        }
    }
}

/*******************************************************************************
 * UTILITY FUNCTIONS
 ******************************************************************************/

/**
 * @brief Get filesystem name
 *
 * @param type  Filesystem type
 * @return Filesystem name
 */
const char* vfs_get_fs_name(fs_type_t type)
{
    switch (type) {
        case FS_TYPE_MINIX3: return "MINIX v3";
        case FS_TYPE_EXT4:   return "ext4";
        case FS_TYPE_F2FS:   return "F2FS";
        case FS_TYPE_PROCFS: return "procfs";
        case FS_TYPE_DEVFS:  return "devfs";
        default:             return "unknown";
    }
}

/**
 * @brief Print mount table
 */
void vfs_print_mounts(void)
{
    printf("================================================================================\n");
    printf("VFS MOUNT TABLE\n");
    printf("================================================================================\n\n");

    if (!g_mounts) {
        printf("No filesystems mounted.\n\n");
    } else {
        printf("%-30s %-10s %-8s\n", "Mount Point", "Type", "Flags");
        printf("--------------------------------------------------------------------------------\n");

        for (struct vfs_mount *m = g_mounts; m; m = m->next) {
            const char *fs_name = vfs_get_fs_name(m->sb->fs_type);

            char flags_str[32] = "";
            if (m->flags & VFS_MOUNT_RDONLY) strcat(flags_str, "ro,");
            if (m->flags & VFS_MOUNT_NOEXEC) strcat(flags_str, "noexec,");
            if (m->flags & VFS_MOUNT_NOSUID) strcat(flags_str, "nosuid,");
            if (m->flags & VFS_MOUNT_NODEV)  strcat(flags_str, "nodev,");

            /* Remove trailing comma */
            size_t len = strlen(flags_str);
            if (len > 0 && flags_str[len - 1] == ',') {
                flags_str[len - 1] = '\0';
            }

            if (flags_str[0] == '\0') {
                strcpy(flags_str, "rw");
            }

            printf("%-30s %-10s %-8s\n", m->mountpoint, fs_name, flags_str);
        }

        printf("\n");
    }

    printf("================================================================================\n");
}
