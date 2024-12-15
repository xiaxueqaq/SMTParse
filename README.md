# SMTParse

## 安装

### 安装 clpoly
----------------

#### 克隆 clpoly 子模块

可以使用 --recursive 参数让子模块自动下载：
```
git clone --recursive <repository-url>
```
如果已经克隆主项目但未递归下载，可以执行：
```
git submodule update --init --recursive
```

#### 编译 clpoly

1. 安装 libboost 和 libgmp
2. 执行
    ```
    cd CLPoly/
    make
    ```

### 安装 smt2_to_maple
-----------------------
执行
```
make smt2_to_maple 
```

**测试**
```
./smt2_to_maple -f test/test.smt2 -o test/test.mpl
```
