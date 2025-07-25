from pathlib import Path

# --- Configuration ---
# 使用脚本自己的位置来确定根目录。
# 这使得脚本无论在哪里运行都能找到正确的相对路径。
BASE_DIR = Path(__file__).parent.resolve()

# 扫描的起始目录，这也是 Lean 库的根。
# import 路径将从这个名字开始。
SCAN_DIR_NAME = 'MiniF2F'

# 最终要写入所有 import 语句的文件。
OUTPUT_FILE_NAME = 'MiniF2F.lean'


def generate_recursive_imports():
    """
    Recursively scans a directory for .lean files and creates a single .lean file
    that imports all of them using their full module path.
    """
    scan_dir = BASE_DIR / SCAN_DIR_NAME
    output_file = BASE_DIR / OUTPUT_FILE_NAME

    # 1. 打印调试信息，确认路径是否正确
    print(f"--- 脚本调试信息 ---")
    print(f"脚本运行根目录 (BASE_DIR): {BASE_DIR}")
    print(f"将要扫描的目录 (scan_dir):   {scan_dir}")
    print(f"将要写入的文件 (output_file): {output_file}")
    print(f"----------------------\n")

    # 2. 验证要扫描的目录是否存在
    if not scan_dir.is_dir():
        print(f"错误: 目录 '{scan_dir}' 不存在或不是一个目录。")
        print("请确认 'MiniF2F' 文件夹与此脚本位于同一目录下。")
        return

    print(f"正在递归扫描目录: {scan_dir}")

    # 3. 递归查找所有 .lean 文件并生成 import 语句
    import_statements = []
    # 使用 rglob('*.lean') 来递归地查找所有匹配的文件
    lean_files = list(scan_dir.rglob('*.lean'))

    if not lean_files:
        print(f"警告: 在 '{scan_dir}' 及其子目录中没有找到任何 .lean 文件。")
        output_file.write_text('', encoding='utf-8')
        print(f"已在 '{output_file}' 创建了一个空文件。")
        return

    print(f"找到 {len(lean_files)} 个 .lean 文件，正在生成 import 语句...")
    for file_path in lean_files:
        # 获取文件相对于根目录的路径
        # 例如: MiniF2F/MiniF2f-test-planner/my_theorem.lean
        relative_path = file_path.relative_to(BASE_DIR)

        # 将路径转换为模块路径
        # 1. 获取所有路径部分: ('MiniF2F', 'MiniF2f-test-planner', 'my_theorem.lean')
        parts = relative_path.parts
        # 2. 移除最后一个部分的 .lean 扩展名
        last_part_no_ext = relative_path.stem
        # 3. 组合成模块路径: ('MiniF2F', 'MiniF2f-test-planner', 'my_theorem')
        module_parts = parts[:-1] + (last_part_no_ext,)
        # 4. 用点连接: "MiniF2F.MiniF2f-test-planner.my_theorem"
        module_path = ".".join(module_parts)
        
        import_line = f"import {module_path}"
        import_statements.append(import_line)

    # 4. 按字母顺序排序，保持文件整洁
    import_statements.sort()

    # 5. 将排序后的 import 语句写入输出文件
    try:
        full_content = '\n'.join(import_statements) + '\n'
        output_file.write_text(full_content, encoding='utf-8')
        print(f"\n成功！已将 {len(import_statements)} 条 import 语句写入到: '{output_file}'")

    except IOError as e:
        print(f"\n错误: 无法写入文件 '{output_file}'。")
        print(f"原因: {e}")

if __name__ == "__main__":
    generate_recursive_imports()