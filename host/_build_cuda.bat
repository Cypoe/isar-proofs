@echo off
call "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Auxiliary\Build\vcvars64.bat" >nul
if errorlevel 1 exit /b 1
nvcc -O2 -o host\emit_work\ir_cuda.exe host\ir_cuda.cu
exit /b %errorlevel%
