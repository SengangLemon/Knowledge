# Linear Algebra (Part I)

Strang의 계산/응용 중심 흐름과 Axler의 구조/증명 중심 흐름을 통합한 집필 목차입니다.  
핵심 원칙은 **직관-계산-구조-응용**의 순환입니다.

## 집필 관점 통합 원칙

- Strang 관점: 선형방정식, 소거법, 직교/최소제곱, 수치/응용을 빠르게 연결
- Axler 관점: 벡터공간, 선형사상, 불변부분공간, 스펙트럴 정리로 구조를 명확화
- 통합 전략: 같은 개념을 `계산적 버전`과 `구조적 버전`으로 2중 제시
- 학습 흐름: 예제 기반 도입 -> 정리와 증명 -> 알고리즘/응용 -> 프로젝트

## 통합 목차 (Draft v1)

### 0. Prelude: Why Linear Algebra
- 선형대수학의 문제 유형 지도
- 좌표 관점 vs 사상(연산자) 관점
- 계산 정확도와 증명 엄밀성의 역할

### 1. Linear Systems and Elimination (Strang-first)
- 연립일차방정식과 행렬 표현
- 가우스 소거법과 LU 분해의 직관
- 해의 존재/유일성, 자유변수와 계수(rank)
- 계산 실습: 소거법 구현과 오차 관찰

### 2. Vector Spaces and Subspaces (Axler-first)
- 벡터공간/부분공간의 공리적 정의
- Span, 선형독립, 생성집합
- 기저와 차원, 좌표 표현의 의미
- 직접합과 부분공간 분해 기초

### 3. Linear Maps and Matrix Representation
- 선형사상의 정의와 예시
- 핵(kernel)과 상(range), rank-nullity 정리
- 기저 변화와 행렬표현의 변환
- 역가능성(동형사상)과 동치 조건

### 4. The Four Fundamental Subspaces + Complete Solution
- 열공간/행공간/영공간/좌영공간
- Ax=b의 전체해 구조 (특수해 + 영공간해)
- RREF, 랭크, 차원 해석
- 네 부분공간의 직교 관계

### 5. Inner Product, Orthogonality, Projection
- 내적공간, 노름, 각도
- 직교기저와 Gram-Schmidt
- 정사영과 최소제곱(Least Squares)
- QR 분해와 데이터 근사

### 6. Determinants Revisited (Late Introduction)
- 결정식의 의미: 부피 스케일/가역성 판별
- 여인수 전개 vs 공리적 성질
- Cramer 공식의 위치와 한계
- Strang식 계산 관점과 Axler식 후기 도입 비교

### 7. Eigenvalues, Invariant Subspaces, Diagonalization
- 고유값/고유벡터와 불변부분공간
- 특성다항식, 최소다항식
- 대각화 가능 조건과 조르당 관점(개요)
- 거듭제곱, 선형동역학, 미분방정식 연결

### 8. Spectral Theorem and SVD
- 자기수반(대칭/Hermitian) 연산자
- 스펙트럴 정리 (실/복소 케이스)
- 특이값분해(SVD)와 유사역행렬
- PCA/저랭크 근사/노이즈 제거

### 9. Operators on Complex Spaces
- 복소벡터공간, unitary/Hermitian
- 정상연산자(normal operator)와 대각화
- 실수 공간과 복소 공간의 비교

### 10. Numerical Linear Algebra
- 조건수와 수치적 안정성
- 부동소수점 오차와 pivoting
- 반복법(기초)과 수렴 개념
- 대규모 문제에서의 분해 선택 기준

### 11. Applications Studio
- 네트워크/그래프/마코프 체인
- 회귀와 최소제곱 기반 모델링
- 신호/푸리에 관점의 선형대수
- 공학 문제(제어, 회로, PDE 이산화) 미니 프로젝트

### 12. Proof Workshop and Capstone
- 핵심 정리 증명 트랙 (rank-nullity, spectral theorem 등)
- 계산 트랙 (LU/QR/SVD 구현 및 비교)
- 통합 캡스톤: 데이터+이론 혼합 보고서

## 권장 장치 (집필 스타일)

- 각 장 시작: `문제 상황 -> 개념 -> 정리 -> 계산 알고리즘 -> 응용`
- 각 장 끝: `Strang Lens`(계산/응용) + `Axler Lens`(구조/증명) 요약
- 연습문제 3층 구조:
  - A형: 계산 숙련
  - B형: 개념/증명
  - C형: 모델링/프로젝트

## 참고한 원본 흐름

- Gilbert Strang, *Linear Algebra and Its Applications* (Ch. 1-8: 소거법/부분공간/직교/결정식/고유값/양정치/수치/최적화)
- Sheldon Axler, *Linear Algebra Done Right* (Ch. 1-9: 벡터공간/선형사상/다항식/고유이론/내적공간/연산자/다중선형/결정식)

> 다음 단계 제안: 위 Draft를 기준으로 12개 장의 상세 섹션(학습목표, 필수정리, 대표예제, 과제)을 1차 버전으로 확장.

## Chapter 본문(정의/예제/풀이/증명/연습문제)

- 통합 본문 파일: `ChapterBook.md`
- 포함 항목:
  - Chapter 1~9 정의
  - 개념 요약
  - 핵심 정리와 증명(또는 증명 스케치)
  - 예제와 풀이
  - 연습문제와 전부 풀이

## Lean 4 Formalization (Axler 기반 간단 버전)

- 프로젝트 루트: `TheMathBook/Part I/Linear Algebra`
- 핵심 파일: `AxlerLean/AxlerSummary.lean`
- 문제 정답 파일: `AxlerLean/Exercises.lean`
- 구성:
  - Ch1-3: 벡터/유한차원/선형사상 기본 정리
  - Ch4: 1차 다항식 평가 정리
  - Ch5: 고유벡터 정의와 nonzero 성질
  - Ch6: 2차원 dot product 대칭성
  - Ch7: 연산자의 덧셈 보존
  - Ch8: 복소수 유사 구조(`Pair`)에서 켤레 involution
  - Ch9: 2x2 determinant의 기본 성질

실행/검증:

```bash
cd "TheMathBook/Part I/Linear Algebra"
lake build
```

## 문제-정답(증명) 사용법

- 형식: 각 문제는 `Problem` 주석 + 바로 아래 `theorem`(정답/증명)으로 구성
- 위치: `AxlerLean/Exercises.lean`의 `namespace Exercises`
- 레벨 구성:
  - `Exercises.Basic` : `p1`~`p6`
  - `Exercises.Standard` : `p7`~`p12`
  - `Exercises.Challenge` : `p13`~`p18`
- 예시 이름:
  - `Exercises.Basic.p1_zero_smul_vec`
  - `Exercises.Standard.p9_map_zero`
  - `Exercises.Challenge.p17_det_equal_rows`
- 목표: Axler 흐름(벡터공간 -> 선형사상 -> 고유값 -> 내적 -> 결정식)을 문제 단위로 빠르게 복습

## LaTeX 동반 문서

- 파일: `latex/Exercises.tex`
- 용도: Lean 문제-정답 파일(`AxlerLean/Exercises.lean`)을 읽기 쉬운 문서 형태로 병행 보관
- 컴파일:
  - `cd "TheMathBook/Part I/Linear Algebra/latex"`
  - `pdflatex Exercises.tex` (또는 `xelatex Exercises.tex`)

### 전체 Lean 변환 문서

- 파일: `latex/LeanAll.tex`
- 범위: 현재 프로젝트의 모든 Lean 파일
  - `AxlerLean.lean`
  - `AxlerLean/AxlerSummary.lean`
  - `AxlerLean/Exercises.lean`
  - `AxlerLean/Basic.lean`
  - `Main.lean`
- 특징: 파일별 역할 설명 + 장별 핵심 정리 이름 + 읽기 순서까지 포함한 사람 친화형 문서
- 컴파일:
  - `cd "TheMathBook/Part I/Linear Algebra/latex"`
  - `pdflatex LeanAll.tex` (또는 `xelatex LeanAll.tex`)
